{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Analysis.WebAssembly.Semantics (
  WasmBody(..), FunctionIndex,
  evalBody, WMonad, WStack, WStackT, WLocals, WGlobals, WasmModule,
  runWithWasmModule, runWithStack, runWithLocals, runWithStub
) where

import Control.Monad.Join (MonadJoin)
import qualified Language.Wasm.Structure as Wasm
import Numeric.Natural (Natural)
import Analysis.WebAssembly.Domain (WValue (..), WDomain, WAddress)
import Prelude hiding (drop)
import Analysis.Monad.Fix (MonadFixpoint (fix))
import Control.Monad.Layer (MonadLayer (upperM), MonadTrans)
import Analysis.Monad (StoreM, MonadCache (..), MapM (..), MapT, runWithMapping)
import Control.Monad.Reader (ReaderT, runReaderT, ask, MonadReader)
import Control.Monad.Identity (IdentityT (..))
import Control.Monad (void)
import qualified Control.Monad.State as S
import qualified Data.Map as M
import Debug.Trace (trace)
import Analysis.Monad.ComponentTracking (spawn, ComponentTrackingM)
import Analysis.Monad.Cache (cached)
import Lattice (BottomLattice(bottom))
import Lattice.Class (Lattice)

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
  | EntryFunction !FunctionIndex
  | BlockBody !Wasm.BlockType !Wasm.Expression
  | LoopBody !Wasm.BlockType !Wasm.Expression
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

returnArityFromIndex :: WasmModule m => FunctionIndex -> m Int
returnArityFromIndex idx = do
  m <- getModule
  let actualType = Wasm.types m !! fromIntegral idx
  return (length (Wasm.results actualType))

blockReturnArity :: WasmModule m => Wasm.BlockType -> m Int
blockReturnArity (Wasm.Inline Nothing) = return 0
blockReturnArity (Wasm.Inline (Just _)) = return 1
blockReturnArity (Wasm.TypeIndex idx) = returnArityFromIndex idx

returnArity :: WasmModule m => WasmBody -> m Int
returnArity (Function idx) = returnArityFromIndex idx
returnArity (EntryFunction idx) = returnArityFromIndex idx
returnArity (BlockBody bt _) = blockReturnArity bt
returnArity (LoopBody bt _) = blockReturnArity bt

-- We cannot rely on MonadFix, because it uses ComponentTracking's call which uses mzero
-- but mzero is not what we want (it would be the empty list). Instead, we want the list containing
-- bottom for each return type
call' :: forall m v . (BottomLattice v, WasmModule m, MonadCache m, MapM (Key m WasmBody) (Val m [v]) m, ComponentTrackingM m (Key m WasmBody)) => WasmBody -> m [v]
call' body = do
  arity <- returnArity body
  k <- key body
  spawn k
  m <- cached @m @WasmBody @[v] k
  maybe (return $ map (const bottom) [0..(arity-1)]) return m -- (map (const bottom) [0..(arity-1)]) return m


-- We need to access the stack
class (WValue v, Monad m) => WStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()
  traceStack :: String -> m ()

newtype WStackT v m a = WStackT { getStackT :: S.StateT [v] m a }
             deriving (Applicative, Monad, Functor, MonadCache, MonadLayer, MonadTrans, MonadJoin, S.MonadState [v])

instance {-# OVERLAPPABLE #-} (WStack m v, MonadLayer t) => WStack (t m) v where
  push = upperM . push
  pop = upperM pop
  traceStack m = upperM (traceStack m)

instance (WValue v, Monad m) => WStack (WStackT v m) v where
  push v = do
    stack <- S.get
    S.put (v : stack)
  pop = do
    stack <- S.get
    case stack of
      first : rest -> S.put rest >> return first
      [] -> error "invalid program does not properly manage its stack"
  traceStack m = do
    stack <- S.get
    trace (m ++ show stack) (return ())

runWithStack :: forall v m a . WStackT v m a -> m (a, [v])
runWithStack = flip S.runStateT [] . getStackT

-- We need to access local variables (local registers)
class (WValue v, Monad m) => WLocals m v | m -> v where
  setLocal :: Natural -> v -> m ()
  getLocal :: Natural -> m v

newtype WLocalsT v m a = WLocalsT { getLocalsT :: S.StateT (M.Map Natural v) m a }
             deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState (M.Map Natural v))

instance {-# OVERLAPPABLE #-} (WLocals m v, MonadLayer t) => WLocals (t m) v where
  setLocal i = upperM . setLocal i
  getLocal = upperM . getLocal

instance (WValue v, Monad m) => WLocals (WLocalsT v m) v where
  getLocal k = do
    locals <- S.get
    case M.lookup k locals of
      Just l -> return l
      Nothing -> error "invalid program does not properly manage its locals"
  setLocal k v = S.get >>= S.put . M.insert k v

runWithLocals :: forall v m a . Monad m => WLocalsT v m a -> m a
runWithLocals l = do
  (r, _) <- S.runStateT (getLocalsT l) M.empty -- no locals initially, this will be populated upon function entry
  return r

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
instance (WValue v, Monad m) => WGlobals (StubT v m) v -- TODO: implement as Map
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
  MonadCache m,
  MapM (Key m WasmBody) (Val m [v]) m,
  ComponentTrackingM m (Key m WasmBody)
  -- MonadFixpoint m WasmBody [v]
  )

evalBody :: forall m a v . WMonad m a v => WasmBody -> m [v]
evalBody = (evalBody' @_ @a) call'

applyFun :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> FunctionIndex -> (Wasm.FuncType -> m [v]) -> m [v]
applyFun rec fidx getArgs = do
  m <- getModule
  let f = Wasm.functions m !! fromIntegral fidx
  let t = Wasm.types m !! fromIntegral (Wasm.funcType f)
  let nParams = length (Wasm.params t)
  let nReturns = length (Wasm.results t)
  let localTypes = Wasm.localTypes f
  let nLocals = length localTypes
  argsv <- getArgs t
  let locals = map zero localTypes
  mapM_ (\(i, v) -> setLocal (fromIntegral i) v) (zip [0..(nParams+nLocals)-1] (argsv++locals)) -- store arguments in locals
  evalFun @m @a rec f -- run the function
  traceStack "after function:"
  reverse <$> mapM (const pop) [0..(nReturns-1)] -- pop the results

evalBody' :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> WasmBody -> m [v]
evalBody' rec (Function fidx) = applyFun @_ @a rec fidx (\t -> reverse <$> mapM (const pop) [0..((length (Wasm.params t))-1)])
evalBody' rec (EntryFunction fidx) = applyFun @_ @a rec fidx (\t -> return $ map top (Wasm.params t))
evalBody' rec (BlockBody bt expr) = do
  nReturns <- blockReturnArity bt
  traceStack "before block body"
  evalExpr @_ @a rec expr
  traceStack "after block body"
  reverse <$> mapM (const pop) [0..(nReturns-1)]
evalBody' rec (LoopBody bt expr) = do
  nReturns <- blockReturnArity bt
  evalExpr @_ @a rec expr
  reverse <$> mapM (const pop) [0..(nReturns-1)]

-- Evaluates a wasm function, leaving its results on the stack
evalFun :: forall m a v . WMonad m a v => (WasmBody -> m [v]) -> Wasm.Function -> m ()
evalFun rec f = evalExpr @m @a rec f.body >> traceStack "after function body:" -- run the function

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
  rec (LoopBody bt loopBody) >>= mapM_ push
evalInstr rec (Wasm.Block bt blockBody) =
  traceStack "before block:" >> rec (BlockBody bt blockBody) >>= mapM_ push >> traceStack "after block:"

evalInstr _ i = todo i
