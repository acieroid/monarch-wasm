{-# LANGUAGE ConstraintKinds #-}
module Analysis.WebAssembly.Domain (
  WValue(..),
  WAddress(..),
  WDomain,
  ) where
import Lattice (SplitLattice)
import Data.Word (Word32, Word64)
import Numeric.Natural (Natural)

-- XXX: What is SplitLattice?
class (Show v, Ord v, SplitLattice v) => WValue v where
  i32 :: Word32 -> v
  i64 :: Word64 -> v
  f32 :: Word32 -> v
  f64 :: Word64 -> v
  func :: Maybe Natural -> v
  extern :: Maybe Natural -> v

class (Show a, Ord a) => WAddress a where
  anyAddr :: a -- TODO: think how to best define it

type WDomain address value = (
  WAddress address,
  WValue value)
