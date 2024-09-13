module Analysis.WebAssembly.Domain where

-- XXX: What is SplitLattice?
class (Show v, Ord v, SplitLattice v) => WValue v where
  any :: v

class (Show a, Ord a) => WAddress a where
  anyAddr :: v -- TODO: think how to best define it

type WDomain address value = (WAddress a, WValue value)
