{-# LANGUAGE ConstraintKinds #-}
module Domain.WebAssembly.Class (
  WValue(..),
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

class (Show v, Ord v, BoolDomain v, Joinable v) => WValue v where
  top :: Wasm.ValueType -> v
  zero :: Wasm.ValueType -> v
  i32 :: Word32 -> v
  i64 :: Word64 -> v
  f32 :: Float -> v
  f64 :: Double -> v
  func :: Maybe Natural -> v
  extern :: Maybe Natural -> v
  iBinOp :: Wasm.BitSize -> Wasm.IBinOp -> v -> v -> v
  fBinOp :: Wasm.BitSize -> Wasm.FBinOp -> v -> v -> v
  iRelOp :: Wasm.BitSize -> Wasm.IRelOp -> v -> v -> v
  fRelOp :: Wasm.BitSize -> Wasm.FRelOp -> v -> v -> v

  -- isTop :: v -> Bool
  -- byte :: Int -> v -> Word8

