{-# LANGUAGE AllowAmbiguousTypes #-}
module Analysis.WebAssembly.Fixpoint (
  analyze,
  WasmCmp
  ) where
import Analysis.WebAssembly.Domain (WDomain, WAddress (..), SingleAddress)
import Analysis.WebAssembly.Semantics (evalFunction, WasmModule, WStack, WLocals, WGlobals, runWithWasmModule, runWithStub)
import Analysis.Monad (CacheT, JoinT, MapM, DependencyTrackingM, WorkListM (..), IntraAnalysisT, runIntraAnalysis, CtxT, MonadCache (Key, Val), StoreM, iterateWL, runWithStore, runWithMapping, runWithDependencyTracking, runWithWorkList)
import Numeric.Natural (Natural)
import Control.Monad.Identity
import Language.Wasm.Structure (Module(..), Export(..), ExportDesc(..))
import Data.Map (Map)
import Data.Function ((&))
import Analysis.Monad.Stack (MonadStack)
import Analysis.Monad.ComponentTracking (ComponentTrackingM, runWithComponentTracking)
import Analysis.Monad.Fix (runFixT)
import Lattice (Meetable, BottomLattice, PartialOrder, Joinable)

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
  WStack m v, -- TODO: isn't WStack a local effect? should be higher in the stack, maybe also in IntraT? but then it becomes part of the component, ...
  WLocals m v,
  WGlobals m v,
  WasmModule m,
  -- MonadFixpoint m Natural [v], -- We don't need this in the inter analysis as it is already satisfied by `runFixT`
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
-- Analyzes all exported function
inter m = mapM_ (\x -> add (x, ())) exportedFuncs >> iterateWL (intra @_ @a)
  where exportedFuncs :: [FunctionIndex]
        exportedFuncs = [ fidx | ExportFunc fidx <- map desc (exports m) ]

-- XXX: the problem with keeping the address polymorphic is that transformers
-- such as `DependencyTrackingM` might overlap once it is instantiated since
-- it could equal `WasmCmp v` for which there already is a transformer on
-- the stack, to solve this, I created a concrete address type.
-- Unfortunately, Haskell does not provide a way to proof type inequality,
-- so this problem can only be solved by providing it with a concrete type
-- (or at least a type whose tag is already known)
-- For this reason, we have a ~ SingleAddress below

-- Analyze a module, returning:
-- - the resulting stack for each function
-- - the linear memory
-- - TODO: the globals
analyze :: forall a v . (a ~ SingleAddress, WDomain a v, Meetable v, BottomLattice v, PartialOrder v, Joinable v) => Module -> (Map (WasmCmp v) [v], Map a v)
analyze m = (returns, store)
  where (((), store), returns) = inter @_ @a m
          & runWithStore @(Map a v) @a @v
          & runWithMapping @(WasmCmp v) @(WasmRes v)
          & runWithDependencyTracking @(WasmCmp v) @a
          & runWithDependencyTracking @(WasmCmp v) @(WasmCmp v)
          & runWithComponentTracking @(WasmCmp v)
          & runWithWorkList @[_] @(WasmCmp v)
          & runWithWasmModule m
          & runWithStub
          & runIdentity
