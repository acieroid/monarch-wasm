{-# LANGUAGE AllowAmbiguousTypes #-}
module Analysis.WebAssembly.Fixpoint (
  analyze,
  WasmCmp
  ) where
import Analysis.WebAssembly.Domain (WDomain, WAddress (..), SingleAddress)
import Analysis.WebAssembly.Semantics (evalBody, WasmModule, WStack, WLocals, WGlobals, runWithWasmModule, runWithStub, WasmBody (..), FunctionIndex, runWithStack, WStackT)
import Analysis.Monad (CacheT, JoinT, MapM, DependencyTrackingM, WorkListM (..), IntraAnalysisT, runIntraAnalysis, CtxT, MonadCache (Key, Val), StoreM, iterateWL, runWithStore, runWithMapping, runWithDependencyTracking, runWithWorkList)
import Control.Monad.Identity
import Language.Wasm.Structure (Module(..), Export(..), ExportDesc(..))
import Data.Map (Map)
import Data.Function ((&))
import Analysis.Monad.Stack (MonadStack)
import Analysis.Monad.ComponentTracking (ComponentTrackingM, runWithComponentTracking)
import Analysis.Monad.Fix (runFixT)
import Lattice (Meetable, BottomLattice, PartialOrder, Joinable)

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
  WasmModule m,
  WStack m v, -- TODO: this is a local concern, but how to express it?
  WLocals m v, -- TODO: this is a local concern, but how to express it?
  WGlobals m v, -- TODO: this is a local concern, but how to express it?
  MapM (WasmCmp v) (WasmRes v) m, -- bodies are mapped to their resulting stack
  -- TODO: dependencies with globals
  ComponentTrackingM m (WasmCmp v),
  DependencyTrackingM m (WasmCmp v) a, -- functions depend on read addresses (TODO: and globals)
  DependencyTrackingM m (WasmCmp v) (WasmCmp v), -- functions depend on called functions
  WorkListM m (WasmCmp v))

type WasmCmp v = Key (IntraT Identity v) WasmBody
type WasmRes v = Val (IntraT Identity v) [v]

intra :: forall m a v . AnalysisM m a v => WasmCmp v -> m ()
intra cmp = runFixT @(IntraT (IntraAnalysisT (WasmCmp v) m) v) (evalBody @_ @a) cmp
           & runIntraAnalysis cmp

inter :: forall m a v . AnalysisM m a v => Module -> m ()
-- TODO: monarch paper defines inter = lftp intra, but I guess this is missing the entry point, hence, we might prefer the following
-- Analyzes all exported function
inter m = mapM_ (\x -> add (Function x, ())) exportedFuncs >> iterateWL (intra @_ @a)
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
  where ((((), store), returns), _) = inter @_ @a m
          & runWithStore @(Map a v) @a @v
          & runWithMapping @(WasmCmp v) @(WasmRes v)
          & runWithDependencyTracking @(WasmCmp v) @a
          & runWithDependencyTracking @(WasmCmp v) @(WasmCmp v)
          & runWithComponentTracking @(WasmCmp v)
          & runWithWorkList @[_] @(WasmCmp v)
          & runWithWasmModule m
          & runWithStub
          & runWithStack
          & runIdentity
