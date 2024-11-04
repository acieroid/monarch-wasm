{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Analysis.WebAssembly.Semantics (
  WasmBody(..), FunctionIndex,
  evalBody, WMonad, WStack, WStackT, WLocals, WGlobals, WasmModule, WEsc, WLinearMemory,
  runWithWasmModule, runWithStack, runWithLocals, runWithGlobals, runWithSingleCellLinearMemory,
) where

import Control.Monad.Join (MonadJoin (..), MonadJoinable(..), msplitOn, condCP, fromBL, mjoins, cond)
import qualified Language.Wasm.Structure as Wasm
import Numeric.Natural (Natural)
import Analysis.WebAssembly.Domain (WValue (..))
import Prelude hiding (break, drop)
import Control.Monad.Layer (MonadLayer (upperM), MonadTrans)
import Analysis.Monad (StoreM, MonadCache (..), MapM (..))
import Control.Monad.Reader (ReaderT, runReaderT, ask, MonadReader)
import Control.Monad.Identity (IdentityT (..))
import qualified Control.Monad.State as S
import qualified Data.Map as M
import Debug.Trace
import Analysis.Monad.ComponentTracking (spawn, ComponentTrackingM)
import Analysis.Monad.Cache (cached)
import Lattice (BottomLattice(bottom), Joinable, joinMap, joins)
import Lattice.Class (Lattice)
import Control.Monad.Escape (MonadEscape(..), escape, catchOn)
import Domain (Domain, BoolDomain (..))
import qualified Data.Set as S
import Lattice.Split (SplitLattice)
import Lattice.ConstantPropagationLattice (CP)
import Data.Maybe (mapMaybe)
import Control.Monad.DomainError (DomainError)

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

instance {-# OVERLAPPABLE #-} (WasmModule m, MonadLayer t, Monad (t m)) => WasmModule (t m) where
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
  maybe (return $ map (const bottom) [0..(arity-1)]) return m

-- We need to access the stack
class (WValue v, Monad m) => WStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()
  fullStack :: m [v]

newtype WStackT v m a = WStackT { getStackT :: S.StateT [v] m a }
             deriving (Applicative, Monad, Functor, MonadCache, MonadLayer, MonadTrans, MonadJoinable, S.MonadState [v])

instance {-# OVERLAPPABLE #-} (WStack m v, MonadLayer t, Monad (t m)) => WStack (t m) v where
  push = upperM . push
  pop = upperM pop
  fullStack = upperM fullStack

instance (WValue v, Monad m) => WStack (WStackT v m) v where
  push v = do
    stack <- S.get
    S.put (v : stack)
  pop = do
    stack <- S.get
    case stack of
      first : rest -> S.put rest >> return first
      [] -> error "invalid program does not properly manage its stack"
  fullStack = reverse <$> S.get

traceWithStack :: (WStack m v) => String -> m a -> m a
traceWithStack msg m = do
    stackBefore <- fullStack
    result <- m
    stackAfter <- fullStack
    trace (msg ++ ": " ++ show stackBefore ++ " -> " ++ show stackAfter) (return result)

runWithStack :: WStackT v m a -> m (a, [v])
runWithStack = flip S.runStateT [] . getStackT

-- We need to access local variables (local registers)
class (WValue v, Monad m) => WLocals m v | m -> v where
  setLocal :: Natural -> v -> m ()
  getLocal :: Natural -> m v

newtype WLocalsT v m a = WLocalsT { getLocalsT :: S.StateT (M.Map Natural v) m a }
             deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState (M.Map Natural v))

instance {-# OVERLAPPABLE #-} (WLocals m v, MonadLayer t, Monad (t m)) => WLocals (t m) v where
  setLocal i = upperM . setLocal i
  getLocal = upperM . getLocal

instance (WValue v, Monad m) => WLocals (WLocalsT v m) v where
  getLocal k = do
    locals <- S.get
    case M.lookup k locals of
      Just l -> return l
      Nothing -> error "invalid program does not properly manage its locals"
  setLocal k v = S.get >>= S.put . M.insert k v

runWithLocals :: Monad m => WLocalsT v m a -> m a
runWithLocals l = do
  (r, _) <- S.runStateT (getLocalsT l) M.empty -- no locals initially, this will be populated upon function entry
  return r

-- We need to access global variables (global registers)
class (WValue v, Monad m) => WGlobals m v | m -> v where
  setGlobal :: Natural -> v -> m ()
  getGlobal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WGlobals m v, MonadLayer t, Monad (t m)) => WGlobals (t m) v where
  setGlobal i = upperM . setGlobal i
  getGlobal = upperM . getGlobal

newtype WGlobalsT v m a = WGlobalsT { getGlobalsT :: S.StateT (M.Map Natural v) m a }
             deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState (M.Map Natural v))

instance (WValue v, Monad m) => WGlobals (WGlobalsT v m) v where
  getGlobal k = do
    globals <- S.get
    case M.lookup k globals of
      Just l -> return l
      Nothing -> error "invalid program does not properly manage its globals"
  setGlobal k v = S.get >>= S.put . M.insert k v

runWithGlobals :: (WasmModule m, WValue v) => WGlobalsT v m a -> m a
runWithGlobals l = do
  m <- getModule
  let globals = zipWith (\idx g -> (idx, runInitializer g)) [0..] (Wasm.globals m)
  (r, _) <- S.runStateT (getGlobalsT l) (M.fromList globals)
  return r
  where runInitializer g = case Wasm.initializer g of
          [Wasm.I32Const n] -> i32 n
          [Wasm.I64Const n] -> i64 n
          [Wasm.F32Const n] -> f32 n
          [Wasm.F64Const n] -> f64 n
          -- ideally we'd call evalExpr and take the top value of the stack, but most initializers are just const, so we specialize it for simplicyt
          _ -> error "unsupported non-const global initializer"

-- We need to access the linear memory (the heap)
class (WValue v, Monad m) => WLinearMemory m v | m -> v where
  load :: Wasm.MemArg -> v -> m v

instance {-# OVERLAPPABLE #-} (WLinearMemory m v, MonadLayer t, Monad (t m)) => WLinearMemory (t m) v where
  load memarg = upperM . load memarg

newtype WSingleCellLinearMemoryT v m a = WLinearMemoryT { getLinearMemoryT :: S.StateT v m a }
  deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState v)

instance (WValue v, Monad m) => WLinearMemory (WSingleCellLinearMemoryT v m) v where
  load _ _ = S.get

runWithSingleCellLinearMemory :: (WValue v, Monad m) => WSingleCellLinearMemoryT v m a -> m a
runWithSingleCellLinearMemory x = do
  (r, _) <- S.runStateT (getLinearMemoryT x) (i32 0)
  return r

data WEsc v = Return ![v]
            | Break !Natural ![v] -- break level and result stack
  deriving (Eq, Ord, Show)

class (Domain esc (WEsc v), Show esc) => WEscape esc v | esc -> v where
  isReturn :: (BoolDomain b, BottomLattice b) => esc -> b
  isBreak :: (BoolDomain b, BottomLattice b, Show b) => esc -> b
  getBreakLevelAndStack :: esc -> [(Natural, [v])]

instance (Ord v, Show v) => WEscape (S.Set (WEsc v)) v where
  isReturn = joinMap $
    \case Return _ -> true
          _ -> false
  isBreak = joinMap $
    \case Break _ _ -> true
          _ -> false
  getBreakLevelAndStack s = mapMaybe extract (S.elems s)
    where extract (Break level stack) = Just (level, stack)
          extract _ = Nothing

type WMonad m v = (
  WasmModule m, -- to access the entire module for type information
  WValue v, -- to abstract the values
  WLinearMemory m v, -- to represent the linear memory
  WStack m v, -- to manipulate the stack
  WLocals m v, -- to manipulate locals
  WGlobals m v, -- to manipulate globals
  MonadJoin m, -- for non-determinism for branching
  MonadCache m,
  MonadEscape m,
  WEscape (Esc m) v,
  SplitLattice (Esc m),
  Domain (Esc m) (WEsc v),
  MapM (Key m WasmBody) (Val m [v]) m,
  ComponentTrackingM m (Key m WasmBody),
  BottomLattice v,
  BottomLattice (Esc m)
  )

evalBody :: WMonad m v => WasmBody -> m [v]
evalBody = evalBody' call'

applyFun :: WMonad m v => (WasmBody -> m [v]) -> FunctionIndex -> (Wasm.FuncType -> m [v]) -> m [v]
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
  traceWithStack ("after function, popping " ++ show nReturns) (evalFun rec f) -- run the function
  reverse <$> mapM (const pop) [0..(nReturns-1)] -- pop the results

evalBody' :: WMonad m v => (WasmBody -> m [v]) -> WasmBody -> m [v]
evalBody' rec (Function fidx) = applyFun rec fidx (\t -> reverse <$> mapM (const pop) [0..((length (Wasm.params t))-1)])
evalBody' rec (EntryFunction fidx) = applyFun rec fidx (return . map top . Wasm.params)
evalBody' rec (BlockBody bt expr) = do
  nReturns <- blockReturnArity bt
  traceWithStack "evalBody' block" $ evalExpr rec expr
  reverse <$> mapM (const pop) [0..(nReturns-1)]
evalBody' rec (LoopBody bt expr) = do
  nReturns <- blockReturnArity bt
  evalExpr rec expr
  reverse <$> mapM (const pop) [0..(nReturns-1)]

-- Evaluates a wasm function, leaving its results on the stack
evalFun :: WMonad m v => (WasmBody -> m [v]) -> Wasm.Function -> m ()
evalFun rec f = evalExpr rec f.body

-- An "expression" is just a sequence of instructions
evalExpr :: WMonad m v => (WasmBody -> m [v]) -> Wasm.Expression -> m ()
evalExpr rec = mapM_ (\i -> traceWithStack (show i) $ evalInstr rec i)

todo :: Wasm.Instruction Natural -> a
todo i = error ("Missing pattern for " ++ show i)

-- This is where the basic semantics are all defined. An interesting aspect will be to handle the loops
evalInstr :: WMonad m v => (WasmBody -> m [v]) -> Wasm.Instruction Natural -> m ()
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
evalInstr _ (Wasm.IRelOp bitSize relOp) = do
  v1 <- pop
  v2 <- pop
  push (iRelOp bitSize relOp v1 v2)
evalInstr rec (Wasm.Loop bt loopBody) = do
  (rec (LoopBody bt loopBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)
          evalInstr rec (Wasm.Loop bt loopBody)

evalInstr rec (Wasm.Block bt blockBody) = do
  (rec (BlockBody bt blockBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)

evalInstr _ (Wasm.Br n) = do
  stack <- fullStack -- extract the full stack to propagate it back to the block we escape from
  escape (Break n stack)

evalInstr rec (Wasm.BrIf n) =
  cond pop (evalInstr rec (Wasm.Br n)) (return ())

evalInstr _ (Wasm.F64Load memarg) = do
  a <- pop
  v <- load memarg a
  push v

evalInstr _ i = todo i

handleBreak :: WMonad m v => ([v] -> m ()) -> Esc m -> m ()
handleBreak onBreak b = mjoins (map (uncurry breakOrReturn) (getBreakLevelAndStack b))
  where breakOrReturn 0 stack = onBreak stack
        breakOrReturn level stack = escape (Break (level - 1) stack)
