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

import Control.Monad.Join (MonadJoin (..), MonadJoinable(..), msplitOn, condCP, fromBL, mjoins, cond, mzero, mjoinMap)
import qualified Language.Wasm.Structure as Wasm hiding (Export(..))
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
import Lattice (BottomLattice(bottom), Joinable (..), joinMap, joins)
import Lattice.Class (Lattice)
import Control.Monad.Escape (MonadEscape(..), escape, catchOn)
import Domain (Domain, BoolDomain (..))
import qualified Data.Set as S
import Lattice.Split (SplitLattice)
import Lattice.ConstantPropagationLattice (CP (..))
import Data.Maybe (mapMaybe)
import Control.Monad.DomainError (DomainError)
import Data.Word (Word64)
import Data.Binary.IEEE754 (wordToDouble, doubleToWord, wordToFloat)

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

pop2 :: (WStack m v) => m (v, v)
pop2 = do
  v1 <- pop
  v2 <- pop
  return (v1, v2)

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
      [] -> error "invalid program does not properly manage its stack (empty when popping)"
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
          -- ideally we'd call evalExpr and take the top value of the stack, but most initializers are just const, so we specialize it for simplicity
          _ -> error "unsupported non-const global initializer"


data Size = Size8 | Size16 | Size32
data Signedness = U | S

-- We need to access the linear memory (the heap)
class (WValue v, Monad m) => WLinearMemory m v | m -> v where
  -- i32.load, i64.load, f32.load, f64.load
  load :: Wasm.ValueType -> Wasm.MemArg -> v -> m v
  -- i32.load8_s, i32.load8_u, i32.load16_s, i32.load16_u, etc.
  load_ :: Wasm.ValueType -> Size -> Signedness -> Wasm.MemArg -> v -> m v
  -- i32.store, i64.store, f32.store, f64.store
  store :: Wasm.ValueType ->  Wasm.MemArg -> (v, v) -> m ()
  -- i32.store8, i32.store16, i64.store8, i64.store16, i64.store32
  store_ :: Wasm.ValueType -> Size -> Wasm.MemArg -> (v, v) -> m ()

instance {-# OVERLAPPABLE #-} (WLinearMemory m v, MonadLayer t, Monad (t m)) => WLinearMemory (t m) v where
  load vt memarg = upperM . load vt memarg
  load_ vt size signed memarg = upperM . load_ vt size signed memarg
  store vt memarg = upperM . store vt memarg
  store_ vt size memarg = upperM . store_ vt size memarg

newtype WTopLinearMemoryT v m a = WLinearMemoryT { getLinearMemoryT :: IdentityT m a }
  deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans)

instance (WValue v, Monad m) => WLinearMemory (WTopLinearMemoryT v m) v where
  load vt _memarg _addr = return (top vt)
  load_ vt _size _signed _memarg _addr = return (top vt)
  store _vt _memarg _addr_v = return ()
  store_ _vt _size _memarg _addr_v = return ()

runWithSingleCellLinearMemory :: (WValue v, Monad m) => WTopLinearMemoryT v m a -> m a
runWithSingleCellLinearMemory x = runIdentityT (getLinearMemoryT x)

-- TODO: try a more precise implementation where memory is a map from i32 to
-- bytes. reading an i32 makes it read 4 bytes. Bytes can be top. Reading the
-- top address returns top.
-- NOTE: memarg offset of 1 means do +1 to the address

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

isFuncImport :: Wasm.Import -> Bool
isFuncImport i = isFuncImport' (Wasm.desc i)
  where isFuncImport' (Wasm.ImportFunc _) = True
        isFuncImport' _ = False

applyFun :: WMonad m v => (WasmBody -> m [v]) -> FunctionIndex -> (Wasm.FuncType -> m [v]) -> m [v]
applyFun rec fidx getArgs = do
  m <- getModule
  let nImportedFuncs = length (filter isFuncImport (Wasm.imports m))
  let f = Wasm.functions m !! (fromIntegral fidx + nImportedFuncs)
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
evalInstr _ (Wasm.I64Const n) = push (i64 n)
evalInstr _ (Wasm.F32Const n) = push (f32 n)
evalInstr _ (Wasm.F64Const n) = push (f64 n)
evalInstr _ Wasm.I32Eqz = do
  v <- pop
  cond (return v) (push (i32 0)) (push (i32 1))
evalInstr _ (Wasm.Select x) = do
  c <- pop
  v1 <- pop
  v2 <- pop
  cond (return c) (push v2) (push v1)
evalInstr _ (Wasm.IBinOp bitSize binOp) = do
  v1 <- pop
  v2 <- pop
  push (iBinOp bitSize binOp v1 v2)
evalInstr _ (Wasm.FBinOp bitSize binOp) = do
  v1 <- pop
  v2 <- pop
  push (fBinOp bitSize binOp v1 v2)
evalInstr _ (Wasm.IRelOp bitSize relOp) = do
  v1 <- pop
  v2 <- pop
  push (iRelOp bitSize relOp v1 v2)
evalInstr _ (Wasm.FRelOp bitSize relOp) = do
  v1 <- pop
  v2 <- pop
  push (fRelOp bitSize relOp v1 v2)
evalInstr rec (Wasm.Loop bt loopBody) = do
  (rec (LoopBody bt loopBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)
          rec (LoopBody bt loopBody) >>= mapM_ push
evalInstr rec (Wasm.Block bt blockBody) = do
  (rec (BlockBody bt blockBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)
evalInstr _ (Wasm.Br n) = do
  stack <- fullStack -- extract the full stack to propagate it back to the block we escape from
  escape (Break n stack)
evalInstr rec (Wasm.BrIf n) = do
  v <- pop
  cond (return v) (evalInstr rec (Wasm.Br n)) (return ())
evalInstr rec (Wasm.BrTable table def) = do
  v <- pop
  -- br_table 1 2 3 means br 1 if the top value is 1, br 2 if the top value is 2, br 3 otherwise
  mjoin
    -- check each element of table for equality
    (mjoinMap (\n -> cond (return (iRelOp Wasm.BS32 Wasm.IEq v (i32 (fromInteger (toInteger n)))))
                          (evalInstr rec (Wasm.Br n))
                          mzero)
      table)
    -- if no elements are equal, go do the default
    -- if all n != v comparisons are definitely true: no elements are equal (must): go to default
    -- if one n != v comparison is definitely false: there is one element equal (must): do not go to default
    -- otherwise: we don't know (may): go to default
    -- so, in short: if a single n != v comparison is false, don't go to default; otherwise go there
    -- TODO: for now, out of simplicity, we always join with default
    (evalInstr rec (Wasm.Br def))

evalInstr _ (Wasm.I32Load memarg) = pop >>= load Wasm.I32 memarg >>= push
evalInstr _ (Wasm.I64Load memarg) = pop >>= load Wasm.I64 memarg >>= push
evalInstr _ (Wasm.F32Load memarg) = pop >>= load Wasm.F32 memarg >>= push
evalInstr _ (Wasm.F64Load memarg) = pop >>= load Wasm.F64 memarg >>= push

evalInstr _ (Wasm.I32Load8S memarg) = pop >>= load_ Wasm.I32 Size8 S memarg >>= push
evalInstr _ (Wasm.I32Load8U memarg) = pop >>= load_ Wasm.I32 Size8 U memarg >>= push
evalInstr _ (Wasm.I32Load16S memarg) = pop >>= load_ Wasm.I32 Size16 S memarg >>= push
evalInstr _ (Wasm.I32Load16U memarg) = pop >>= load_ Wasm.I32 Size16 U memarg >>= push
evalInstr _ (Wasm.I64Load8S memarg) = pop >>= load_ Wasm.I64 Size8 S memarg >>= push
evalInstr _ (Wasm.I64Load8U memarg) = pop >>= load_ Wasm.I64 Size8 U memarg >>= push
evalInstr _ (Wasm.I64Load16S memarg) = pop >>= load_ Wasm.I64 Size16 S memarg >>= push
evalInstr _ (Wasm.I64Load16U memarg) = pop >>= load_ Wasm.I64 Size16 U memarg >>= push
evalInstr _ (Wasm.I64Load32S memarg) = pop >>= load_ Wasm.I64 Size32 S memarg >>= push
evalInstr _ (Wasm.I64Load32U memarg) = pop >>= load_ Wasm.I64 Size32 U memarg >>= push
evalInstr _ (Wasm.I32Store memarg) = pop2 >>= store Wasm.I32 memarg
evalInstr _ (Wasm.I64Store memarg) = pop2 >>= store Wasm.I64 memarg
evalInstr _ (Wasm.F32Store memarg) = pop2 >>= store Wasm.F32 memarg
evalInstr _ (Wasm.F64Store memarg) = pop2 >>= store Wasm.F64 memarg
evalInstr _ (Wasm.I32Store8 memarg) = pop2 >>= store_ Wasm.I32 Size8 memarg
evalInstr _ (Wasm.I32Store16 memarg) = pop2 >>= store_ Wasm.I32 Size16 memarg
evalInstr _ (Wasm.I64Store8 memarg) = pop2 >>= store_ Wasm.I64 Size8 memarg
evalInstr _ (Wasm.I64Store16 memarg) = pop2 >>= store_ Wasm.I64 Size16 memarg
evalInstr _ (Wasm.I64Store32 memarg) = pop2 >>= store_ Wasm.I64 Size32 memarg
evalInstr rec (Wasm.Call f) =
  rec (Function f) >>= mapM_ push
evalInstr rec (Wasm.If bt consequent alternative) = do
  v <- pop
  cond (return v) (rec (BlockBody bt consequent) >>= mapM_ push) (rec (BlockBody bt alternative) >>= mapM_ push)

evalInstr _ i = todo i

handleBreak :: WMonad m v => ([v] -> m ()) -> Esc m -> m ()
handleBreak onBreak b = mjoins (map (uncurry breakOrReturn) (getBreakLevelAndStack b))
  where breakOrReturn 0 stack = onBreak stack
        breakOrReturn level stack = escape (Break (level - 1) stack)
