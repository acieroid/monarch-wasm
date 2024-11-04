{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
module Analysis.WebAssembly.Domain (
  WValue(..),
  ConstPropValue,
  ) where
import Lattice (Joinable (..), PartialOrder (..), BottomLattice (..))
import Data.Word (Word32, Word64)
import Numeric.Natural (Natural)
import Lattice.Class (Meetable (..))
import Language.Wasm.Structure (BitSize (..), IBinOp (..))
import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, rotateL, rotateR, Bits)
import qualified Language.Wasm.Structure as Wasm
import Lattice.ConstantPropagationLattice (CP(..))

class (Show v, Ord v) => WValue v where
  top :: Wasm.ValueType -> v
  zero :: Wasm.ValueType -> v
  i32 :: Word32 -> v
  i64 :: Word64 -> v
  f32 :: Float -> v
  f64 :: Double -> v
  func :: Maybe Natural -> v
  extern :: Maybe Natural -> v
  iBinOp :: BitSize -> IBinOp -> v -> v -> v

-- Implements binary operations on i32/i64
-- XXX: This does not perfectly follow the WebAssembly semantics, for simplicity.
concreteiBinOp :: (Bits b, Integral b) => IBinOp -> b -> b -> b
concreteiBinOp IAdd = (+)
concreteiBinOp ISub = (-)
concreteiBinOp IMul = (*)
concreteiBinOp IDivU = div
concreteiBinOp IDivS = div
concreteiBinOp IRemU = rem
concreteiBinOp IRemS = rem
concreteiBinOp IAnd = (.&.)
concreteiBinOp IOr = (.|.)
concreteiBinOp IXor = xor
concreteiBinOp IShl = \x y -> shiftL x (fromIntegral y)
concreteiBinOp IShrU = \x y -> shiftR x (fromIntegral y)
concreteiBinOp IShrS = \x y -> shiftR x (fromIntegral y)
concreteiBinOp IRotl = \x y -> rotateL x (fromIntegral y)
concreteiBinOp IRotr = \x y -> rotateR x (fromIntegral y)

data ConstPropValue =
    Bottom
  | I32 !(CP Word32)
  | I64 !(CP Word64)
  | F32 !(CP Float)
  | F64 !(CP Double)
  | Func !(CP (Maybe Natural))
  | Extern !(CP (Maybe Natural))
  deriving (Show, Ord, Eq)

instance WValue ConstPropValue where
  top Wasm.I32 = I32 Top
  top Wasm.I64 = I64 Top
  top Wasm.F32 = F32 Top
  top Wasm.F64 = F64 Top
  top Wasm.Func = Func Top
  top Wasm.Extern = Extern Top
  zero Wasm.I32 = I32 (Constant 0)
  zero Wasm.I64 = I64 (Constant 0)
  zero Wasm.F32 = F32 (Constant 0)
  zero Wasm.F64 = F64 (Constant 0)
  zero Wasm.Func = error "should not happen?"
  zero Wasm.Extern = error "should not happen"
  i32 n = I32 (Constant n)
  i64 n = I64 (Constant n)
  f32 n = F32 (Constant n)
  f64 n = F64 (Constant n)
  func n = Func (Constant n)
  extern n = Extern (Constant n)
  iBinOp BS32 binOp (I32 (Constant x)) (I32 (Constant y)) = I32 (Constant (concreteiBinOp binOp x y))
  iBinOp BS32 _ (I32 _) (I32 _) = I32 Top
  iBinOp BS64 binOp (I64 (Constant x)) (I64 (Constant y)) = I64 (Constant (concreteiBinOp binOp x y))
  iBinOp BS32 _ (I64 _) (I64 _) = I64 Top
  iBinOp _ _ _ _ = error "should never mistype binary operation"

instance Joinable ConstPropValue where
  join Bottom x = x
  join x Bottom = x
  join (I32 x) (I32 y) = I32 (join x y)
  join (I64 x) (I64 y) = I64 (join x y)
  join (F32 x) (F32 y) = F32 (join x y)
  join (F64 x) (F64 y) = F64 (join x y)
  join (Func x) (Func y) = Func (join x y)
  join (Extern x) (Extern y) = Extern (join x y)
  join x y = error $ "should never join elements of different types" ++ show x ++ ", " ++ show y

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
