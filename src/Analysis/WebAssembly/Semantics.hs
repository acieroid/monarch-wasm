{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Analysis.WebAssembly.Semantics (
  WasmBody(..), FunctionIndex,
  evalBody, WMonad, WStack, WLocals, WGlobals, WasmModule,
  runWithWasmModule, runWithStub
) where

import Control.Monad.Join (MonadJoin)
import qualified Language.Wasm.Structure as Wasm
import Numeric.Natural (Natural)
import Analysis.WebAssembly.Domain (WValue (..), WDomain, WAddress)
import Prelude hiding (drop)
import Analysis.Monad.Fix (MonadFixpoint (fix))
import Control.Monad.Layer (MonadLayer (upperM), MonadTrans)
import Analysis.Monad (StoreM, MonadCache)
import Control.Monad.Reader (ReaderT, runReaderT, ask, MonadReader)
import Control.Monad.Identity (IdentityT (..))
import Analysis.Monad.ComponentTracking (call)
import Control.Monad (void)

type FunctionIndex = Natural -- as used in wasm package

-- We need a few Ord instances to get Ord on our WasmBody
deriving instance Ord Wasm.ValueType
deriving instance Ord Wasm.BlockType
deriving instance Ord Wasm.ElemType
deriving instance Ord Wasm.MemArg
deriving instance Ord Wasm.IUnOp
deriving instance Ord Wasm.IBinOp
deriving instance Ord Wasm.IRelOp
deriving instance Ord Wasm.FUnOp
deriving instance Ord Wasm.FBinOp
deriving instance Ord Wasm.FRelOp
deriving instance Ord Wasm.BitSize
deriving instance Ord (Wasm.Instruction Natural)

data WasmBody =
    Function !FunctionIndex
  | BlockBody !Wasm.Expression
  deriving (Show, Eq, Ord)

-- A reader-like monad to get access to the entire program. Necessary to e.g., access types, jump targets, etc.
class Monad m => WasmModule m where
  getModule :: m Wasm.Module

instance {-# OVERLAPPABLE #-} (WasmModule m, MonadLayer t) => WasmModule (t m) where
  getModule = upperM getModule

newtype WasmModuleT m a = WasmModuleT (ReaderT Wasm.Module m a)
                        deriving (Functor, Applicative, Monad, MonadTrans, MonadLayer, MonadReader Wasm.Module)
runWithWasmModule :: Wasm.Module -> WasmModuleT m a -> m a
runWithWasmModule r (WasmModuleT m) = runReaderT m r

instance (Monad m) => WasmModule (WasmModuleT m) where
   getModule = ask

numberOfReturnValues :: WasmModule m => Wasm.Function -> m Int
numberOfReturnValues f = do
  m <- getModule
  let actualType = Wasm.types m !! fromIntegral (Wasm.funcType f)
  return (length (Wasm.results actualType))

-- We need to access the stack
class (WValue v, Monad m) => WStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()

instance {-# OVERLAPPABLE #-} (WStack m v, MonadLayer t) => WStack (t m) v where
  push = upperM . push
  pop = upperM pop

-- We need to access local variables (local registers)
class (WValue v, Monad m) => WLocals m v | m -> v where
  setLocal :: Natural -> v -> m ()
  getLocal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WLocals m v, MonadLayer t) => WLocals (t m) v where
  setLocal i = upperM . setLocal i
  getLocal = upperM . getLocal

-- We need to access global variables (global registers)
class (WValue v, Monad m) => WGlobals m v | m -> v where
  setGlobal :: Natural -> v -> m ()
  getGlobal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WGlobals m v, MonadLayer t) => WGlobals (t m) v where
  setGlobal i = upperM . setGlobal i
  getGlobal = upperM . getGlobal


-- TODO: these are just stub instances for WStack, WGlobals and WLocals
-- implement these with a suitable instance, perhaps split them up too,
-- as they might need to be at different locations in the monad stack.
newtype StubT v m a = StubT { getStubT :: IdentityT m a }
             deriving (Applicative, Monad, Functor, MonadCache, MonadLayer, MonadTrans, MonadJoin)
instance (WValue v, Monad m) => WStack (StubT v m) v
instance (WValue v, Monad m) => WLocals (StubT v m) v
instance (WValue v, Monad m) => WGlobals (StubT v m) v
runWithStub :: forall v m a . StubT v m a -> m a
runWithStub = runIdentityT . getStubT

-- We need to access the linear memory (the heap)
type WLinearMemory m a v = StoreM m a v

type WMonad m a v = (
  WAddress a,
  WasmModule m, -- to access the entire module for type information
  WDomain a v, -- to abstract the values
  WLinearMemory m a v, -- to represent the linear memory
  WStack m v, -- to manipulate the stack
  WLocals m v, -- to manipulate locals
  WGlobals m v, -- to manipulate globals
  MonadJoin m, -- for non-determinism for branching (still TODO)
  MonadFixpoint m WasmBody [v])

evalBody :: forall m a v . WMonad m a v => WasmBody -> m [v]
evalBody = fix (evalBody' @_ @a)

evalBody' :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> WasmBody -> m [v]
evalBody' rec (Function fidx) = evalFunction @_ @a rec fidx
evalBody' rec (BlockBody expr) = evalExpr @_ @a rec expr >> return [] -- TODO: block arity

-- Eval a function from its index
evalFunction :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> FunctionIndex -> m [v]
evalFunction rec fidx = do
  m <- getModule
  let f = Wasm.functions m !! fromIntegral fidx
  evalFun @m @a rec f

-- Evaluates a wasm function, returns the return values of the functions, by truncating the stack
evalFun :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> Wasm.Function -> m [v]
evalFun rec f = do
  _ <- evalExpr @m @a rec f.body
  nReturns <- numberOfReturnValues f
  mapM (const pop) [0..nReturns]

-- An "expression" is just a sequence of instructions
evalExpr :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> Wasm.Expression -> m ()
evalExpr rec = mapM_ (evalInstr @m @a rec)

todo :: Wasm.Instruction Natural -> a
todo i = error ("Missing pattern for " ++ show i)

-- This is where the basic semantics are all defined. An interesting aspect will be to handle the loops
evalInstr :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> Wasm.Instruction Natural -> m ()
evalInstr _ Wasm.Unreachable = return ()
evalInstr _ Wasm.Nop = return ()
evalInstr _ (Wasm.RefNull Wasm.FuncRef) = push (func Nothing)
evalInstr _ (Wasm.RefNull Wasm.ExternRef) = push (extern Nothing)
evalInstr _ Wasm.Drop = drop
evalInstr _ (Wasm.GetLocal i) = getLocal i >>= push
evalInstr _ (Wasm.SetLocal i) = pop >>= setLocal i
evalInstr _ (Wasm.TeeLocal i) = do
  v <- pop
  push v
  setLocal i v
evalInstr _ (Wasm.GetGlobal i) = getGlobal i >>= push
evalInstr _ (Wasm.SetGlobal i) = pop >>= setGlobal i
evalInstr _ (Wasm.I32Const n) = push (i32 n)
evalInstr _ (Wasm.IBinOp bitSize binOp) = do
  v1 <- pop
  v2 <- pop
  push (iBinOp bitSize binOp v1 v2)
evalInstr rec (Wasm.Loop bt loopBody) =
 void $ rec (BlockBody loopBody)

evalInstr _ i = todo i
