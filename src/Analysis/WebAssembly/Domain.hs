{-# LANGUAGE ConstraintKinds #-}
module Analysis.WebAssembly.Domain (
  WValue(..),
  WAddress(..),
  WDomain,
  ConstPropValue,
  SingleAddress,
  ) where
import Lattice (Joinable (..), PartialOrder (..), BottomLattice (..))
import Data.Word (Word32, Word64)
import Numeric.Natural (Natural)
import Lattice.Class (Meetable (..))

class (Show v, Ord v) => WValue v where
  i32 :: Word32 -> v
  i64 :: Word64 -> v
  f32 :: Word32 -> v
  f64 :: Word64 -> v
  func :: Maybe Natural -> v
  extern :: Maybe Natural -> v

-- Similar to a CP lattice, but without bottom. Isomorphic to Maybe, but we prefer explicit names
data ConstOrTop a =
    Constant a
  | Top
  deriving (Show, Ord, Eq)

instance Ord a => Joinable (ConstOrTop a) where
  join v@(Constant x) (Constant y) | x == y = v
  join _ _ = Top

data ConstPropValue =
    Bottom
  | I32 (ConstOrTop Word32)
  | I64 (ConstOrTop Word64)
  | F32 (ConstOrTop Word32)
  | F64 (ConstOrTop Word64)
  | Func (ConstOrTop (Maybe Natural))
  | Extern (ConstOrTop (Maybe Natural))
  deriving (Show, Ord, Eq)

instance WValue ConstPropValue where
  i32 n = I32 (Constant n)
  i64 n = I64 (Constant n)
  f32 n = F32 (Constant n)
  f64 n = F64 (Constant n)
  func n = Func (Constant n)
  extern n = Extern (Constant n)

instance Joinable ConstPropValue where
  join (I32 x) (I32 y) = I32 (join x y)
  join (I64 x) (I64 y) = I64 (join x y)
  join (F32 x) (F32 y) = F32 (join x y)
  join (F64 x) (F64 y) = F64 (join x y)
  join (Func x) (Func y) = Func (join x y)
  join (Extern x) (Extern y) = Extern (join x y)
  join _ _= error "should never join elements of different types"

instance Meetable ConstPropValue where
  meet v@(I32 x) (I32 y) | x == y = v
  meet v@(I64 x) (I64 y) | x == y = v
  meet v@(F32 x) (F32 y) | x == y = v
  meet v@(F64 x) (F64 y) | x == y = v
  meet v@(Func x) (Func y) | x == y = v
  meet v@(Extern x) (Extern y) | x == y = v
  meet _ _ = Bottom

instance PartialOrder ConstPropValue where
  leq (I32 x) (I32 y) = leq x y
  leq (I64 x) (I64 y) = leq x y
  leq (F32 x) (F32 y) = leq x y
  leq (F64 x) (F64 y) = leq x y
  leq (Func x) (Func y) = leq x y
  leq (Extern x) (Extern y) = leq x y
  leq _ _ = False

instance BottomLattice ConstPropValue where
  bottom = Bottom

class (Show a, Ord a) => WAddress a where
  anyAddr :: a -- TODO: think how to best define it

-- A naive modeling of addresses, where all addresses are equal
type SingleAddress = ()
instance WAddress SingleAddress where
  anyAddr = ()

type WDomain address value = (
  WAddress address,
  WValue value)
