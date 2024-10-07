{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
module Analysis.WebAssembly.Semantics (
  evalFunction, WMonad, WStack, WLocals, WGlobals, WasmModule
) where

import Control.Monad.Join (MonadJoin)
import Language.Wasm.Structure (Module, Function(body), Expression, types, funcType, results, Instruction (..), ElemType (..), functions)
import Numeric.Natural (Natural)
import Analysis.WebAssembly.Domain (WValue (..), WDomain, WAddress)
import Prelude hiding (drop)
import Analysis.Monad.Fix (MonadFixpoint)
import Control.Monad.Layer (MonadLayer (upperM))
import Analysis.Monad (StoreM)

-- A reader-like monad to get access to the entire program. Necessary to e.g., access types, jump targets, etc.
class Monad m => WasmModule m where
  getModule :: m Module

instance {-# OVERLAPPABLE #-} (WasmModule m, MonadLayer t) => WasmModule (t m) where
  getModule = upperM getModule

numberOfReturnValues :: WasmModule m => Function -> m Int
numberOfReturnValues f = do
  m <- getModule
  let actualType = types m !! fromIntegral (funcType f)
  return (length (results actualType))

-- We need to access the stack
class (WValue v, Monad m) => WStack m v | m -> v where
  push :: v -> m ()
  pop :: m v
  drop :: m ()
  drop = do
    _ <- pop
    return ()

instance {-# OVERLAPPABLE #-} (WStack m v, MonadLayer t) => WStack (t m) v where
  push = upperM . push
  pop = upperM pop

-- We need to access local variables (local registers)
class (WValue v, Monad m) => WLocals m v | m -> v where
  setLocal :: Natural -> v -> m ()
  getLocal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WLocals m v, MonadLayer t) => WLocals (t m) v where
  setLocal i = upperM . setLocal i
  getLocal = upperM . getLocal

-- We need to access global variables (global registers)
class (WValue v, Monad m) => WGlobals m v | m -> v where
  setGlobal :: Natural -> v -> m ()
  getGlobal :: Natural -> m v

instance {-# OVERLAPPABLE #-} (WGlobals m v, MonadLayer t) => WGlobals (t m) v where
  setGlobal i = upperM . setGlobal i
  getGlobal = upperM . getGlobal

-- We need to access the linear memory (the heap)
type WLinearMemory m a v = StoreM m a v

type WMonad m a v = (
  WAddress a,
  WasmModule m, -- to access the entire module for type information
  WDomain a v, -- to abstract the values
  WLinearMemory m a v, -- to represent the linear memory
  WStack m v, -- to manipulate the stack
  WLocals m v, -- to manipulate locals
  WGlobals m v, -- to manipulate globals
  MonadJoin m, -- for non-determinism for branching (still TODO)
  MonadFixpoint m Natural [v])

-- Eval a function from its index
evalFunction :: forall m a v . WMonad m a v => Natural -> m [v]
evalFunction fidx = do
  m <- getModule
  let f = functions m !! fromIntegral fidx
  evalFun @m @a f

-- Evaluates a wasm function, returns the return values of the functions, by truncating the stack
evalFun :: forall m a v . WMonad m a v => Function -> m [v] -- TODO: wouldn't m () be enough here? Probably not because we want to cache return values
evalFun f = do
  _ <- evalExpr @m @a f.body
  nReturns <- numberOfReturnValues f
  mapM (const pop) [0..nReturns]

-- An "expression" is just a sequence of instructions
evalExpr :: forall m a v . WMonad m a v => Expression -> m ()
evalExpr = mapM_ (evalInstr @m @a)

-- This is where the basic semantics are all defined. An interesting aspect will be to handle the loops
evalInstr :: WMonad m a v => Instruction Natural -> m ()
evalInstr Nop = return ()
-- TODO: if, block, etc.
-- TODO: call
evalInstr (RefNull FuncRef) = push (func Nothing)
evalInstr (RefNull ExternRef) = push (extern Nothing)
-- TODO: RefIsNull
-- TODO: RefFunc index
evalInstr Drop = drop
evalInstr (GetLocal i) = getLocal i >>= push
evalInstr (SetLocal i) = pop >>= setLocal i
evalInstr (TeeLocal i) = do
  v <- pop
  push v
  setLocal i v
evalInstr (GetGlobal i) = getGlobal i >>= push
evalInstr (SetGlobal i) = pop >>= setGlobal i
-- TODO: load instructions
-- TODO: store instructions
-- TODO: MemorySize
-- TODO: MemoryGrow
-- TODO: MemoryFill
-- TODO: MemoryCopy
