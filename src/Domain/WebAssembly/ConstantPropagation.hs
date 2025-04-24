module Domain.WebAssembly.ConstantPropagation(
    ConstPropValue
  ) where

import Lattice (Joinable (..), PartialOrder (..), BottomLattice (..))
import Numeric.IEEE (IEEE, copySign, minNum, maxNum, identicalIEEE)
import Data.Word (Word8, Word32, Word64)
import Numeric.Natural (Natural)
import Lattice.Class (Meetable (..))
import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, rotateL, rotateR, Bits)
import qualified Language.Wasm.Structure as Wasm
import Lattice.ConstantPropagationLattice (CP(..))
import Domain (BoolDomain, Domain)
import Domain.Class (Domain(..))
import Domain.Core (BoolDomain(..))
import Lattice (justOrBot)
import Control.Monad.Join (cond)
import Domain.WebAssembly.Class

-- Implements binary operations on i32/i64. Heavily inspired from haskell-wasm's interpreter
concreteiBinOp :: (Bits b, Integral b) => Wasm.IBinOp -> Wasm.BitSize -> b -> b -> b
concreteiBinOp Wasm.IAdd _ v1 v2 = v1 + v2
concreteiBinOp Wasm.ISub _ v1 v2 = v1 - v2
concreteiBinOp Wasm.IMul _ v1 v2 = v1 * v2
concreteiBinOp Wasm.IDivU _ v1 v2 = v1 `quot` v2
concreteiBinOp Wasm.IDivS bs v1 v2 = asWordBitSize bs $ asIntBitSize bs v1 `quot` asIntBitSize bs v2
concreteiBinOp Wasm.IRemU _ v1 v2 = v1 `rem` v2
concreteiBinOp Wasm.IRemS bs v1 v2 = asWordBitSize bs $ asIntBitSize bs v1 `rem` asIntBitSize bs v2
concreteiBinOp Wasm.IAnd _ v1 v2 = v1 .&. v2
concreteiBinOp Wasm.IOr _ v1 v2 = v1 .|. v2
concreteiBinOp Wasm.IXor _ v1 v2 = v1 `xor` v2
concreteiBinOp Wasm.IShl bs v1 v2 = v1 `shiftL` (fromIntegral v2 `rem` bitSize bs)
concreteiBinOp Wasm.IShrU bs v1 v2 = v1 `shiftR` (fromIntegral v2 `rem` bitSize bs)
concreteiBinOp Wasm.IShrS bs v1 v2 = error "TODO: shrs" -- asWordBitSize bs $ asIntBitSize bs v1 `shiftR` (fromIntegral v2 `rem` bitSize bs)
concreteiBinOp Wasm.IRotl _ v1 v2 = v1 `rotateL` fromIntegral v2
concreteiBinOp Wasm.IRotr _ v1 v2 = v1 `rotateR` fromIntegral v2

concretefBinOp :: IEEE b => Wasm.FBinOp -> Wasm.BitSize -> b -> b -> b
concretefBinOp Wasm.FAdd _ v1 v2 = v1 + v2
concretefBinOp Wasm.FSub _ v1 v2 = v1 - v2
concretefBinOp Wasm.FMul _ v1 v2 = v1 * v2
concretefBinOp Wasm.FMin _ v1 v2 = zeroAwareMin v1 v2
concretefBinOp Wasm.FMax _ v1 v2 = zeroAwareMax v1 v2
concretefBinOp Wasm.FCopySign _ v1 v2 = copySign v1 v2

concreteiRelOp :: (Bits b, Integral b) => Wasm.IRelOp -> Wasm.BitSize -> b -> b -> b
concreteiRelOp Wasm.IEq _ v1 v2 = if v1 == v2 then 1 else 0
concreteiRelOp Wasm.INe _ v1 v2 = if v1 /= v2 then 0 else 1
concreteiRelOp Wasm.ILtU _ v1 v2 = if v1 < v2 then 1 else 0
concreteiRelOp Wasm.ILtS bs v1 v2 = if asIntBitSize bs v1 < asIntBitSize bs v2 then 1 else 0
concreteiRelOp Wasm.IGtU _ v1 v2 = if v1 > v2 then 1 else 0
concreteiRelOp Wasm.IGtS bs v1 v2 = if asIntBitSize bs v1 > asIntBitSize bs v2 then 1 else 0
concreteiRelOp Wasm.ILeU _ v1 v2 = if v1 <= v2 then 1 else 0
concreteiRelOp Wasm.ILeS bs v1 v2 = if asIntBitSize bs v1 <= asIntBitSize bs v2 then 1 else 0
concreteiRelOp Wasm.IGeU _ v1 v2 = if v1 >= v2 then 1 else 0
concreteiRelOp Wasm.IGeS bs v1 v2 = if asIntBitSize bs v1 >= asIntBitSize bs v2 then 1 else 0

concretefRelOp :: IEEE b => Wasm.FRelOp -> Wasm.BitSize -> b -> b -> b
concretefRelOp Wasm.FEq _ v1 v2 = if v1 == v2 then 1 else 0
concretefRelOp Wasm.FNe _ v1 v2 = if v1 /= v2 then 0 else 1
concretefRelOp Wasm.FLt _ v1 v2 = if v1 < v2 then 1 else 0
concretefRelOp Wasm.FGt _ v1 v2 = if v1 > v2 then 1 else 0
concretefRelOp Wasm.FLe _ v1 v2 = if v1 <= v2 then 1 else 0
concretefRelOp Wasm.FGe _ v1 v2 = if v1 >= v2 then 1 else 0

asInt32 :: (Integral b1, Integral b2) => b1 -> b2
asInt32 w =
    if w < 0x80000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFF - w + 1)

asInt64 :: (Integral b1, Integral b2) => b1 -> b2
asInt64 w =
    if w < 0x8000000000000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFFFFFFFFFF - w + 1)

asWord32 :: (Integral b1, Integral b2) => b1 -> b2
asWord32 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFF - (fromIntegral (abs i)) + 1

asWord64 :: (Integral b1, Integral b2) => b1 -> b2
asWord64 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFFFFFFFFFF - (fromIntegral (abs i)) + 1

asIntBitSize :: (Integral b1, Integral b2) => Wasm.BitSize -> b1 -> b2
asIntBitSize Wasm.BS32 = asInt32
asIntBitSize Wasm.BS64 = asInt64

asWordBitSize :: (Integral b1, Integral b2) => Wasm.BitSize -> b1 -> b2
asWordBitSize Wasm.BS32 = asWord32
asWordBitSize Wasm.BS64 = asWord64

bitSize Wasm.BS32 = 32
bitSize Wasm.BS64 = 64
nearest :: (IEEE a) => a -> a
nearest f
    | isNaN f = f
    | f >= 0 && f <= 0.5 = copySign 0 f
    | f < 0 && f >= -0.5 = -0
    | otherwise =
        let i = floor f :: Integer in
        let fi = fromIntegral i in
        let r = abs f - abs fi in
        flip copySign f (
            if r == 0.5
            then (
                case (even i, f < 0) of
                    (True, _) -> fi
                    (_, True) -> fi - 1.0
                    (_, False) -> fi + 1.0
            )
            else fromIntegral (round f :: Integer)
        )

zeroAwareMin :: IEEE a => a -> a -> a
zeroAwareMin a b
    | identicalIEEE a 0 && identicalIEEE b (-0) = b
    | isNaN a = a
    | isNaN b = b
    | otherwise = minNum a b

zeroAwareMax :: IEEE a => a -> a -> a
zeroAwareMax a b
    | identicalIEEE a (-0) && identicalIEEE b 0 = b
    | isNaN a = a
    | isNaN b = b
    | otherwise = maxNum a b

data ConstPropValue =
    Bottom
  | I32 !(CP Word32)
  | I64 !(CP Word64)
  | F32 !(CP Float)
  | F64 !(CP Double)
  | Func !(CP (Maybe Natural))
  | Extern !(CP (Maybe Natural))
  deriving (Show, Ord, Eq)

instance Domain ConstPropValue Bool where
  inject True = I32 (Constant 1)
  inject False = I32 (Constant 0)

instance BoolDomain ConstPropValue where
  isTrue (I32 (Constant 0)) = False
  isTrue (I32 _) = True
  isTrue (I64 (Constant 0)) = False
  isTrue (I64 _) = True
  isTrue (F32 (Constant 0)) = False
  isTrue (F32 _) = True
  isTrue (F64 (Constant 0)) = False
  isTrue (F64 _) = True
  isTrue _ = False
  isFalse (I32 (Constant 0)) = True
  isFalse (I32 (Constant _)) = False
  isFalse (I32 Top) = True
  isFalse (I64 (Constant 0)) = True
  isFalse (I64 (Constant _)) = False
  isFalse (I64 _) = True
  isFalse (F32 (Constant 0)) = True
  isFalse (F32 (Constant _)) = False
  isFalse (F32 _) = True
  isFalse (F64 (Constant 0)) = True
  isFalse (F64 (Constant _)) = False
  isFalse (F64 _) = True
  isFalse _ = False
  or a b = justOrBot $ cond (pure a) (pure a) (pure b)
  and a b = justOrBot $ cond (pure a) (cond (pure b) (pure b) (pure false)) (pure false)
  not v = join t f
     where t = if isTrue  v then inject False else bottom
           f = if isFalse v then inject True else bottom

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
  iBinOp Wasm.BS32 binOp (I32 (Constant x)) (I32 (Constant y)) = I32 (Constant (concreteiBinOp binOp Wasm.BS32 x y))
  iBinOp Wasm.BS32 _ (I32 _) (I32 _) = I32 Top
  iBinOp Wasm.BS64 binOp (I64 (Constant x)) (I64 (Constant y)) = I64 (Constant (concreteiBinOp binOp Wasm.BS64 x y))
  iBinOp Wasm.BS64 _ (I64 _) (I64 _) = I64 Top
  iBinOp _ _ _ _ = error "iBinOp: should never mistype binary operation"
  fBinOp Wasm.BS32 binOp (F32 (Constant x)) (F32 (Constant y)) = F32 (Constant (concretefBinOp binOp Wasm.BS32 x y))
  fBinOp Wasm.BS32 _ (F32 _) (F32 _) = F32 Top
  fBinOp Wasm.BS64 binOp (F64 (Constant x)) (F64 (Constant y)) = F64 (Constant (concretefBinOp binOp Wasm.BS64 x y))
  fBinOp Wasm.BS64 _ (F64 _) (F64 _) = F64 Top
  fBinOp bs binOp x y = error ("fBinOp: should never mistype binary operation" ++ show [show bs, show binOp, show x, show y])
  iRelOp Wasm.BS32 relOp (I32 (Constant x)) (I32 (Constant y)) = I32 (Constant (concreteiRelOp relOp Wasm.BS32 x y))
  iRelOp Wasm.BS32 _ (I32 _) (I32 _) = I32 Top
  iRelOp Wasm.BS64 relOp (I64 (Constant x)) (I64 (Constant y)) = I64 (Constant (concreteiRelOp relOp Wasm.BS64 x y))
  iRelOp Wasm.BS64 _ (I64 _) (I64 _) = I64 Top
  iRelOp _ _ _ _ = error "iRelOp: should never mistype relational operation"

  fRelOp Wasm.BS32 relOp (F32 (Constant x)) (F32 (Constant y)) = F32 (Constant (concretefRelOp relOp Wasm.BS32 x y))
  fRelOp Wasm.BS32 _ (F32 _) (F32 _) = F32 Top
  fRelOp Wasm.BS64 relOp (F64 (Constant x)) (F64 (Constant y)) = F64 (Constant (concretefRelOp relOp Wasm.BS64 x y))
  fRelOp Wasm.BS64 _ (F64 _) (F64 _) = F64 Top
  fRelOp _ _ _ _ = error "iRelOp: should never mistype relational operation"

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
