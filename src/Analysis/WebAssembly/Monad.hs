{-# LANGUAGE UndecidableInstances, LambdaCase #-}
module Analysis.WebAssembly.Monad where

import Analysis.Monad.Cache
import Analysis.Monad.ComponentTracking (spawn, ComponentTrackingM)
import Analysis.Monad.Map
import Control.Monad.Escape (MonadEscape(..), escape, catchOn)
import Control.Monad.Layer
import Control.Monad.Identity (IdentityT (..))
import Control.Monad.Join
import Control.Monad.Reader
import Control.Monad.State (MonadState)
import qualified Control.Monad.State as S
import qualified Data.Set as S
import Data.Functor
import qualified Data.Map as M
import Data.Maybe
import Domain.Core.BoolDomain
import Domain.Class
import Domain.WebAssembly.Class
import qualified Language.Wasm.Structure as Wasm hiding (Export(..))
import Lattice.Class hiding (top)
import Lattice.Split
import Numeric.Natural (Natural)

-- | Types of function indices
type FunctionIndex = Natural -- as used in wasm package

-- | Components of a WebAssembly analysis
data WasmBody v =
    Function      !FunctionIndex ![v]
  | EntryFunction !FunctionIndex
  | BlockBody     !Wasm.BlockType !Wasm.Expression
  | LoopBody      !Wasm.BlockType !Wasm.Expression
  deriving (Show, Eq, Ord)

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

-- TODO: move to a 'Common' module
data Size = Size8 | Size16 | Size32
data Signedness = U | S

------------------------------------------------------------
-- WasmModule
------------------------------------------------------------

-- | A reader-like monad to get access to the entire program. Necessary to e.g., access types, jump targets, etc.
class Monad m => WasmModule m where
  getModule :: m Wasm.Module

instance {-# OVERLAPPABLE #-} (WasmModule m, MonadLayer t, Monad (t m)) => WasmModule (t m) where
  getModule = upperM getModule

-- | Trivial instance of 'WasModule' based on the reader monad
newtype WasmModuleT m a = WasmModuleT (ReaderT Wasm.Module m a)
                        deriving (Functor, Applicative, Monad, MonadTrans, MonadLayer, MonadReader Wasm.Module)
instance (Monad m) => WasmModule (WasmModuleT m) where
   getModule = ask

-- | Run the given computation in the context of a 'WasmModuleT' monad
-- transformer.
runWithWasmModule :: Wasm.Module -> WasmModuleT m a -> m a
runWithWasmModule r (WasmModuleT m) = runReaderT m r

-- | Lookup the arity of the type of at the given index,
-- uses the implicit module available in the context.
returnArityFromTypeIndex :: WasmModule m => Wasm.TypeIndex -> m Int
returnArityFromTypeIndex idx = do
  m <- getModule
  let tidx = fromIntegral idx
  if tidx >= length (Wasm.types m) then
    error ("unknown type: " ++ show idx)
  else
    return (length (Wasm.results (Wasm.types m !! tidx)))

-- | Lookup the arity of a function at the given index,
-- uses the implicit module available in the context.
returnArityFromFunctionIndex :: WasmModule m => FunctionIndex -> m Int
returnArityFromFunctionIndex idx = do
  m <- getModule
  let fidx = fromIntegral idx
  if fidx >= length (Wasm.functions m) then
    error ("unknown function: " ++ show m)
  else
    returnArityFromTypeIndex (Wasm.funcType (Wasm.functions m !! fidx))

-- | Compute the arity of the given block type.
blockReturnArity :: WasmModule m => Wasm.BlockType -> m Int
blockReturnArity (Wasm.Inline Nothing) = return 0
blockReturnArity (Wasm.Inline (Just _)) = return 1
blockReturnArity (Wasm.TypeIndex idx) = returnArityFromTypeIndex idx

-- | Compute the arity of arbitrary types.
returnArity :: WasmModule m => WasmBody v -> m Int
returnArity (Function idx _) = returnArityFromFunctionIndex idx
returnArity (EntryFunction idx) = returnArityFromFunctionIndex idx
returnArity (BlockBody bt _) = blockReturnArity bt
returnArity (LoopBody bt _) = blockReturnArity bt

-- | Compute the arity for the given function.
functionArity :: WasmModule m => Wasm.Function -> m Int
functionArity f = returnArityFromTypeIndex (Wasm.funcType f)

------------------------------------------------------------
-- Stack
------------------------------------------------------------

-- | Access to the WebAssembly stack
class (WValue v, Monad m) => WStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()
  fullStack :: m [v]
  popAll :: m [v]

-- | Pops two elements from the stack
pop2 :: (WStack m v) => m (v, v)
pop2 = liftA2 (,) pop pop

instance {-# OVERLAPPABLE #-} (WStack m v, MonadLayer t, Monad (t m)) => WStack (t m) v where
  push = upperM . push
  pop = upperM pop
  fullStack = upperM fullStack
  popAll = upperM popAll

-- | WebAssembly Stack based on the state monad 
newtype WStackT v m a = WStackT { getStackT :: S.StateT [v] m a }
             deriving (Applicative, Monad, Functor, MonadCache, MonadLayer, MonadTrans, MonadJoinable, S.MonadState [v])

instance (WValue v, Monad m) => WStack (WStackT v m) v where
  push v = S.modify (v:) 
  pop = do
    stack <- S.get
    case stack of
      first : rest -> S.put rest $> first
      [] -> error "invalid program does not properly manage its stack (empty when popping)"
  fullStack = reverse <$> S.get
  popAll = fullStack <* S.put []

runWithStack :: WStackT v m a -> m (a, [v])
runWithStack = flip S.runStateT [] . getStackT

------------------------------------------------------------
-- Local Variables
------------------------------------------------------------

-- | Access local variables (registers) from WebAssembly
class (WValue v, Monad m) => WLocals m v | m -> v where
  setLocal :: Natural -> v -> m ()
  getLocal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WLocals m v, MonadLayer t, Monad (t m)) => WLocals (t m) v where
  setLocal i = upperM . setLocal i
  getLocal = upperM . getLocal

-- | Trivial instance of 'WLocals' based on the state monad
newtype WLocalsT v m a = WLocalsT { getLocalsT :: S.StateT (M.Map Natural v) m a }
             deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState (M.Map Natural v))

instance (WValue v, Monad m) => WLocals (WLocalsT v m) v where
  getLocal k = do
    locals <- S.get
    case M.lookup k locals of
      Just l -> return l
      Nothing -> error "invalid program does not properly manage its locals"
  setLocal k v = S.get >>= S.put . M.insert k v

-- | Run the given computation in a 'WLocalsT' context giving
-- access to local variables initially empty and populated
-- upon each function entry. 
runWithLocals :: Monad m => WLocalsT v m a -> m a
runWithLocals = flip S.evalStateT M.empty . getLocalsT

------------------------------------------------------------
-- Global variables
------------------------------------------------------------

-- | Access global variables from WebAssembly
class (WValue v, Monad m) => WGlobals m v | m -> v where
  setGlobal :: Natural -> v -> m ()
  getGlobal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WGlobals m v, MonadLayer t, Monad (t m)) => WGlobals (t m) v where
  setGlobal i = upperM . setGlobal i
  getGlobal = upperM . getGlobal

-- | Trivial instance of 'WGlobals' based on the state monad
newtype WGlobalsT v m a = WGlobalsT { getGlobalsT :: S.StateT (M.Map Natural v) m a }
             deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans, S.MonadState (M.Map Natural v))

instance (WValue v, Monad m) => WGlobals (WGlobalsT v m) v where
  getGlobal k = do
    globals <- S.get
    case M.lookup k globals of
      Just l -> return l
      Nothing -> error "invalid program does not properly manage its globals"
  setGlobal k v = S.get >>= S.put . M.insert k v

-- | Runs the given computation ina 'WGlobalST' monadic context by
-- initializing the global memory according to initializer expressions
-- in WebAssembly module, thus it requires 'WasmModule' to get
-- access to the initializer expressions.
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

------------------------------------------------------------
-- Linear memory
------------------------------------------------------------

-- | Access to WebAssembly's linear memory
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

-- | Form of linear memory that returns the top value for every memory access
newtype WTopLinearMemoryT v m a = WLinearMemoryT { getLinearMemoryT :: IdentityT m a }
  deriving (Applicative, Monad, Functor, MonadLayer, MonadTrans)

instance (WValue v, Monad m) => WLinearMemory (WTopLinearMemoryT v m) v where
  load vt _memarg _addr = return (top vt)
  load_ vt _size _signed _memarg _addr = return (top vt)
  store _vt _memarg _addr_v = return ()
  store_ _vt _size _memarg _addr_v = return ()

-- | Run the given computation in a 'WTopLinearMemoryT' mondaci context
runWithSingleCellLinearMemory :: (WValue v, Monad m) => WTopLinearMemoryT v m a -> m a
runWithSingleCellLinearMemory = runIdentityT . getLinearMemoryT

-- TODO: try a more precise implementation where memory is a map from i32 to
-- bytes. reading an i32 makes it read 4 bytes. Bytes can be top. Reading the
-- top address returns top.
-- NOTE: memarg offset of 1 means do +1 to the address

------------------------------------------------------------
-- Escaping control flow
------------------------------------------------------------

data WEsc v = Return ![v]
            | Break !Natural ![v] -- break level and result stack
  deriving (Eq, Ord, Show)

class (Domain esc (WEsc v), Show esc) => WEscape esc v | esc -> v where
  isReturn :: (BoolDomain b, BottomLattice b) => esc -> b
  isBreak :: (BoolDomain b, BottomLattice b, Show b) => esc -> b
  getBreakLevelAndStack :: esc -> [(Natural, [v])]
  getReturnStack :: esc -> [[v]]

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
  getReturnStack s = mapMaybe extract (S.elems s)
    where extract (Return stack) = Just stack
          extract _ = Nothing

------------------------------------------------------------
-- WebAssembly Monad
------------------------------------------------------------

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
    MapM (Key m (WasmBody v)) (Val m [v]) m,
    ComponentTrackingM m (Key m (WasmBody v)),
    BottomLattice v,
    BottomLattice (Esc m)
  )

