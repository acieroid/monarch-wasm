module Analysis.WebAssembly.Fixpoint where

type AnalysisM m address value = (
  WDomain value,
  MapM FunctionIndex [value] m, -- functions are mapped to their return stack
  -- XXX: do we need component tracking, if we already know all components statically?
  DependencyTracking m FunctionIndex address, -- functions depend on read addresses (TODO: and globals)
  DependencyTracking m FunctionIndex FunctionIndex, -- functions depend on called functions
  WorkListM m FunctionIndex)


intra :: AnalysisM m address value => FunctionIndex -> m ()
intra fidx = _

inter :: AnalysisM m address value => Module -> m ()
inter m = _

-- Analyze a module, returning:
-- - the resulting stack for each function
-- - the linear memory
-- - TODO: the globals
analyze :: WDomain value => Module -> (Map FunctionIndex [value], Map address value)
