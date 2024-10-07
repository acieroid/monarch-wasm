{-# LANGUAGE AllowAmbiguousTypes #-}
module Analysis.WebAssembly.Fixpoint where
import Analysis.WebAssembly.Domain (WDomain, WAddress)
import Analysis.WebAssembly.Semantics (evalFunction, WasmModule, WStack, WLocals, WGlobals)
import Analysis.Monad (CacheT, JoinT, MapM, DependencyTrackingM, WorkListM (..), IntraAnalysisT, runIntraAnalysis, CtxT, MonadCache (Key, Val), StoreM, iterateWL, runWithStore, runWithMapping, runWithDependencyTracking, runWithWorkList)
import Numeric.Natural (Natural)
import Control.Monad.Identity
import Language.Wasm (Module)
import Data.Map (Map)
import Data.Function ((&))
import Analysis.Monad.Stack (MonadStack)
import Analysis.Monad.ComponentTracking (ComponentTrackingM, runWithComponentTracking)
import Analysis.Monad.Fix (MonadFixpoint, runFixT)
import Lattice (Meetable, BottomLattice, PartialOrder, Joinable)
import Language.Wasm.Structure (StartFunction(..), start)
import Data.Set (Set)

type FunctionIndex = Natural -- as used in wasm package

type IntraT m v = MonadStack '[
    CtxT (),
    JoinT,
    CacheT
  ] m

-- AnalysisM represents the constraints remaining after the intra (i.e., global concerns)
type AnalysisM m a v = (
  Meetable v,
  WAddress a,
  StoreM m a v,
  WStack m v,
  WLocals m v,
  WGlobals m v,
  WasmModule m,
  MonadFixpoint m Natural [v],
  MapM (WasmCmp v) (WasmRes v) m, -- functions are mapped to their return stack
  -- XXX: do we need component tracking, if we already know all components statically? (assuming loops are fixed points)
  ComponentTrackingM m (WasmCmp v),
  DependencyTrackingM m (WasmCmp v) a, -- functions depend on read addresses (TODO: and globals)
  DependencyTrackingM m (WasmCmp v) (WasmCmp v), -- functions depend on called functions
  WorkListM m (WasmCmp v))

type WasmCmp v = Key (IntraT Identity v) FunctionIndex
type WasmRes v = Val (IntraT Identity v) [v]

intra :: forall m a v . AnalysisM m a v => WasmCmp v -> m ()
intra fidx = runFixT @(IntraT (IntraAnalysisT (WasmCmp v) m) v) (evalFunction @_ @a) fidx
  & runIntraAnalysis fidx

inter :: forall m a v . AnalysisM m a v => Module -> m ()
-- TODO: monarch paper defines inter = lftp intra, but I guess this is missing the entry point, hence, we might prefer the following
inter m = case start m of
            Just (StartFunction fidx) ->
              -- Start analyzing at the entry point
              add (fidx, ()) >> iterateWL (intra @_ @a)
            Nothing ->
              -- No entry point, no analysis!
              return ()

-- Analyze a module, returning:
-- - the resulting stack for each function
-- - the linear memory
-- - TODO: the globals
analyze :: forall a v . (WDomain a v, BottomLattice v, PartialOrder v, Joinable v) => Module -> (Map FunctionIndex [v], Map a v)
analyze m = (returns, store)
  where (((), store), returns) = inter m
          & runWithStore @(Map a v) @a @v
          & runWithMapping @(WasmCmp v) @(WasmRes v)
          & runWithDependencyTracking @(WasmCmp v) @v
          & _ -- TODO: Hole added here to make error more explicit: I get a "• Could not deduce (WorkListM m0 (Natural, ()))", where (Natural, ()) corresponds to WasmCmp v
          & runWithDependencyTracking @(WasmCmp v) @(WasmCmp v)
          & runWithComponentTracking @(WasmCmp v)
          & runWithWorkList @(Set (WasmCmp v))
          & runIdentity
