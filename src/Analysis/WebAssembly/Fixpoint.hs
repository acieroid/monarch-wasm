{-# LANGUAGE AllowAmbiguousTypes #-}
module Analysis.WebAssembly.Fixpoint (
  analyze,
  WasmCmp,
  WasmRes
  ) where
import Analysis.WebAssembly.Semantics (evalBody, WasmModule, WStack, WLocals, WGlobals, runWithWasmModule, runWithGlobals, WasmBody (..), FunctionIndex, runWithStack, runWithLocals, WEsc, WLinearMemory, runWithSingleCellLinearMemory)
import Analysis.Monad (CacheT, JoinT, MapM, DependencyTrackingM, MonadDependencyTracking, WorkListM (..), IntraAnalysisT, runIntraAnalysis, CtxT, MonadCache (Key, Val), iterateWL, runWithStore, runWithMapping, runWithDependencyTracking, runWithWorkList)
import Control.Monad.Identity
import Language.Wasm.Structure (Module(..), Export(..), ExportDesc(..))
import Data.Map (Map)
import Data.Function ((&))
import Analysis.Monad.Stack (MonadStack)
import Analysis.Monad.ComponentTracking (ComponentTrackingM, runWithComponentTracking)
import Analysis.Monad.Fix (runFixT)
import Lattice (Meetable, BottomLattice, Joinable)
import Control.Monad.Escape (MayEscapeT)
import Data.Set (Set)
import Analysis.WebAssembly.Domain (WValue)
import Data.Typeable

type IntraT m v = MonadStack '[
    MayEscapeT (Set (WEsc v)),
    CtxT (),
    JoinT,
    CacheT
  ] m

-- InterM represents the constraints remaining after the intra (i.e., global concerns)
type InterM m v = (
  Typeable v,
  Meetable v,
  WasmModule m,
  WLinearMemory m v,
  WStack m v, -- TODO: no need for the stack in the global concerns, can be moved to local only
  WLocals m v, -- We need locals as a global concern, as locals are scoped to functions, which may include multiple blocks
  WGlobals m v,
  MapM (WasmCmp v) (WasmRes v) m, -- bodies are mapped to their resulting stack
  -- TODO: dependencies with globals
  ComponentTrackingM m (WasmCmp v),
  -- DependencyTrackingM m (WasmCmp v) v, -- TODO: functions depend on read addresses
  -- TODO: functions depend on globals
  MonadDependencyTracking (WasmCmp v) (WasmCmp v) m, -- functions depend on called functions
  WorkListM m (WasmCmp v),
  BottomLattice v,
  Joinable v
  )

type WasmCmp v = Key (IntraT Identity v) (WasmBody v)
type WasmRes v = Val (IntraT Identity v) [v]

intra :: forall m v . InterM m v => WasmCmp v -> m ()
intra cmp = runFixT @(IntraT (IntraAnalysisT (WasmCmp v) m) v) evalBody cmp
           & runIntraAnalysis cmp

inter :: forall m v . InterM m v => Module -> m ()
-- Analyzes all exported function
inter m = mapM_ (\x -> add (EntryFunction x, ())) exportedFuncs >> iterateWL intra
  where exportedFuncs :: [FunctionIndex]
        exportedFuncs = [ fidx | ExportFunc fidx <- map desc (exports m) ]

-- Analyze a module, returning:
-- - the resulting stack for each function
-- - the linear memory
analyze :: forall v . (Typeable v, WValue v, Meetable v, BottomLattice v, Joinable v) => Module -> (Map (WasmCmp v) (WasmRes v), Map v v)
analyze m = (returns, store)
  where ((((), store), returns), _) = inter @_ @v m
          & runWithStore @(Map v v) @v
          & runWithMapping @(WasmCmp v) @(WasmRes v)
          -- & runWithDependencyTracking @(WasmCmp v) @v
          & runWithDependencyTracking @(WasmCmp v) @(WasmCmp v)
          & runWithComponentTracking @(WasmCmp v)
          & runWithWorkList @[_] @(WasmCmp v)
          & runWithGlobals
          & runWithWasmModule m
          & runWithStack
          & runWithLocals
          & runWithSingleCellLinearMemory
          & runIdentity
