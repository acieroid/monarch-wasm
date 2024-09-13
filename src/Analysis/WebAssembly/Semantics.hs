module Analysis.WebAssembly.Semantics (
  evalFun
) where
import Lattice (SplitLattice)
import Control.Monad.Join (MonadJoin)
import Language.Wasm.Structure (Module, Function(body), Expression, types, funcType, results, Instruction (Nop))
import GHC.Natural (Natural)


-- A reader-like monad to get access to the entire program. Necessary to e.g., access types, jump targets, etc.
class Monad m => WasmModule m where
  getModule :: m Module

numberOfReturnValues :: WasmModule m => Function -> m Int
numberOfReturnValues f = do
  m <- getModule
  let actualType = types m !! fromIntegral (funcType f)
  return (length (results actualType))

class (WValue v, Monad m) => WasmStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()

type WMonad m value = (
  WasmModule m, -- to access the entire module for type information
  WDomain value, -- to abstract the values
  WasmStack m value, -- to manipulate the stack
  MonadJoin m -- for non-determinism
  -- XXX: what is MonadCache?
  -- XXX: what is ComponentTrackingM?
  -- TODO: locals and globals, these are just a finite number of registers
  -- TODO: linear memory, could be abstracted by a single cell at first
    )

-- Evaluates a wasm function, returns the return values of the functions, by truncating the stack
evalFun :: WMonad m v => Function -> m [v] -- TODO: wouldn't m () be enough here?
evalFun f = do
  _ <- evalExpr (body f)
  nReturns <- numberOfReturnValues f
  mapM (const pop) [0..nReturns]

-- An "expression" is just a sequence of instructions
evalExpr :: WMonad m v => Expression -> m ()
evalExpr = mapM_ evalInstr

evalInstr :: WMonad m v => Instruction Natural -> m ()
evalInstr Nop = return ()
