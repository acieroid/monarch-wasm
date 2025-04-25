{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Analysis.WebAssembly.Semantics (
  WasmBody(..), FunctionIndex,
  evalBody, WMonad, WStack, WStackT, WLocals, WGlobals, WasmModule, WEsc, WLinearMemory,
  runWithWasmModule, runWithStack, runWithLocals, runWithGlobals, runWithSingleCellLinearMemory,
) where

import Control.Monad.Join (MonadJoin (..), MonadJoinable(..), msplitOn, condCP, fromBL, mjoins, cond, mbottom, mjoinMap)
import qualified Language.Wasm.Structure as Wasm hiding (Export(..))
import Numeric.Natural (Natural)
import Domain.WebAssembly.Class(WValue (..))
import Prelude hiding (break, drop)
import Control.Monad.Layer (MonadLayer (upperM), MonadTrans)
import Analysis.Monad (StoreM, MonadCache (..), MapM (..))
import Control.Monad.Reader (ReaderT, runReaderT, ask, MonadReader)
import Control.Monad.Identity (IdentityT (..))
import qualified Control.Monad.State as S
import qualified Data.Map as M
import Debug.Trace
import Analysis.Monad.ComponentTracking (spawn, ComponentTrackingM)
import Analysis.Monad.Cache (cached)
import Lattice (BottomLattice(bottom), Joinable (..), joinMap, joins)
import Lattice.Class (Lattice)
import Control.Monad.Escape (MonadEscape(..), escape, catchOn)
import Domain (Domain, BoolDomain (..))
import qualified Data.Set as S
import Lattice.Split (SplitLattice)
import Lattice.ConstantPropagationLattice (CP (..))
import Data.Maybe (mapMaybe)
import Control.Monad.DomainError (DomainError)
import Data.Word (Word64)
import Data.Binary.IEEE754 (wordToDouble, doubleToWord, wordToFloat)
import Analysis.WebAssembly.Monad

-- We cannot rely on MonadFix, because it uses ComponentTracking's call which uses mbottom
-- but mbottom is not what we want (it would be the empty list). Instead, we want the list containing
-- bottom for each return type
call' :: forall m v . (BottomLattice v, WasmModule m, MonadCache m, MapM (Key m (WasmBody v)) (Val m [v]) m, ComponentTrackingM m (Key m (WasmBody v))) => WasmBody v -> m [v]
call' body = do
  arity <- returnArity body
  k <- key body
  spawn k
  m <- cached @m @(WasmBody v) @[v] k
  maybe (return $ map (const bottom) [0..(arity-1)]) return m


traceWithStack :: (WStack m v) => String -> m a -> m a
traceWithStack msg m = do
    stackBefore <- fullStack
    result <- m
    stackAfter <- fullStack
    trace (msg ++ ": " ++ show stackBefore ++ " -> " ++ show stackAfter) (return result)

evalBody :: WMonad m v => WasmBody v -> m [v]
evalBody = evalBody' call'

isFuncImport :: Wasm.Import -> Bool
isFuncImport i = isFuncImport' (Wasm.desc i)
  where isFuncImport' (Wasm.ImportFunc _) = True
        isFuncImport' _ = False


checkEmptyStack :: WMonad m v => m ()
checkEmptyStack = do
  s <- fullStack
  if null s then return () else error $ "stack not empty" ++ show s


getFunction :: WMonad m v => FunctionIndex -> m Wasm.Function
getFunction fidx = do
  m <- getModule
  let nImportedFuncs = length (filter isFuncImport (Wasm.imports m))
  let realIdx = fromIntegral fidx + nImportedFuncs
  return $ Wasm.functions m !! realIdx

getFunctionType :: WMonad m v => Wasm.Function -> m Wasm.FuncType
getFunctionType fun = do
  m <- getModule
  return $ Wasm.types m !! fromIntegral (Wasm.funcType fun)

applyFun :: WMonad m v => (WasmBody v -> m [v]) -> FunctionIndex -> (Wasm.FuncType -> [v]) -> m [v]
applyFun rec fidx getArgs = do
  fun <- getFunction fidx
  t <- getFunctionType fun
  let nParams = length (Wasm.params t)
  let nReturns = length (Wasm.results t)
  let localTypes = Wasm.localTypes fun
  let nLocals = length localTypes

  let argsv = getArgs t
  let locals = map zero localTypes
  mapM_ (\(i, v) -> setLocal (fromIntegral i) v) (zip [0..(nParams+nLocals)-1] (argsv++locals)) -- store arguments in locals
  traceWithStack ("---\nevalFun" ++ show fidx ++ "\n---")  $ evalFun rec fun -- run the function
  res <- reverse <$> mapM (const pop) [0..(nReturns-1)] -- pop the results
  _ <- popAll -- functions can leave value on the stack that are not part of the return value. Get rid of them.
  return res

evalBody' :: WMonad m v => (WasmBody v -> m [v]) -> WasmBody v -> m [v]
evalBody' rec (Function fidx args) = applyFun rec fidx (const args)
evalBody' rec (EntryFunction fidx) = applyFun rec fidx (map top . Wasm.params)
evalBody' rec (BlockBody bt expr) = do
  nReturns <- blockReturnArity bt
  evalExpr rec expr
  reverse <$> mapM (const pop) [0..(nReturns-1)]
evalBody' rec (LoopBody bt expr) = do
  nReturns <- blockReturnArity bt
  evalExpr rec expr
  reverse <$> mapM (const pop) [0..(nReturns-1)]

-- Evaluates a wasm function, leaving its results on the stack
evalFun :: WMonad m v => (WasmBody v -> m [v]) -> Wasm.Function -> m ()
evalFun rec f = traceShow f evalExpr rec f.body `catchOn` (fromBL . isReturn, handleReturn @_ handler)
  where handler stack = do
          arity <- functionArity f
          mapM_ push (take arity stack)

-- An "expression" is just a sequence of instructions
evalExpr :: WMonad m v => (WasmBody v -> m [v]) -> Wasm.Expression -> m ()
evalExpr rec = mapM_ (\i -> traceWithStack ("evalInstr " ++ show i) (evalInstr rec i))

todo :: Wasm.Instruction Natural -> a
todo i = error ("Missing pattern for " ++ show i)

-- This is where the basic semantics are all defined. An interesting aspect will be to handle the loops
evalInstr :: WMonad m v => (WasmBody v -> m [v]) -> Wasm.Instruction Natural -> m ()
evalInstr _ Wasm.Unreachable = return ()
evalInstr _ Wasm.Nop = return ()
evalInstr _ (Wasm.RefNull Wasm.FuncRef) = push (func Nothing)
evalInstr _ (Wasm.RefNull Wasm.ExternRef) = push (extern Nothing)
evalInstr _ Wasm.Drop = drop
evalInstr _ (Wasm.GetLocal i) = getLocal i >>= push
evalInstr _ (Wasm.SetLocal i) = pop >>= setLocal i
evalInstr _ (Wasm.TeeLocal i) = do
  v <- pop
  push v
  setLocal i v
evalInstr _ (Wasm.GetGlobal i) = getGlobal i >>= push
evalInstr _ (Wasm.SetGlobal i) = pop >>= setGlobal i
evalInstr _ (Wasm.I32Const n) = push (i32 n)
evalInstr _ (Wasm.I64Const n) = push (i64 n)
evalInstr _ (Wasm.F32Const n) = push (f32 n)
evalInstr _ (Wasm.F64Const n) = push (f64 n)
evalInstr _ Wasm.I32Eqz = do
  v <- pop
  cond (return v) (push (i32 0)) (push (i32 1))
evalInstr _ (Wasm.Select x) = do
  c <- pop
  v1 <- pop
  v2 <- pop
  cond (return c) (push v2) (push v1)
evalInstr _ (Wasm.IBinOp bitSize binOp) = do
  v1 <- pop
  v2 <- pop
  push (iBinOp bitSize binOp v1 v2)
evalInstr _ (Wasm.FBinOp bitSize binOp) = do
  v1 <- pop
  v2 <- pop
  push (fBinOp bitSize binOp v1 v2)
evalInstr _ (Wasm.IRelOp bitSize relOp) = do
  v1 <- pop
  v2 <- pop
  push (iRelOp bitSize relOp v1 v2)
evalInstr _ (Wasm.FRelOp bitSize relOp) = do
  v1 <- pop
  v2 <- pop
  push (fRelOp bitSize relOp v1 v2)
evalInstr rec (Wasm.Loop bt loopBody) = do
  (rec (LoopBody bt loopBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)
          rec (LoopBody bt loopBody) >>= mapM_ push
evalInstr rec (Wasm.Block bt blockBody) = do
  (rec (BlockBody bt blockBody) >>= mapM_ push) `catchOn` (fromBL . isBreak, handleBreak @_ f)
  where f stack = do
          arity <- blockReturnArity bt
          mapM_ push (take arity stack)
evalInstr _ Wasm.Return = popAll >>= (escape . Return)
evalInstr _ (Wasm.Br n) = popAll >>= (escape . Break n)
evalInstr rec (Wasm.BrIf n) = do
  v <- pop
  cond (return v) (evalInstr rec (Wasm.Br n)) (return ())
evalInstr rec (Wasm.BrTable table def) = do
  v <- pop
  -- br_table 1 2 3 means br 1 if the top value is 1, br 2 if the top value is 2, br 3 otherwise
  mjoin
    -- check each element of table for equality
    (mjoinMap (\n -> cond (return (iRelOp Wasm.BS32 Wasm.IEq v (i32 (fromInteger (toInteger n)))))
                          (evalInstr rec (Wasm.Br n))
                          mbottom)
      table)
    -- if no elements are equal, go do the default
    -- if all n != v comparisons are definitely true: no elements are equal (must): go to default
    -- if one n != v comparison is definitely false: there is one element equal (must): do not go to default
    -- otherwise: we don't know (may): go to default
    -- so, in short: if a single n != v comparison is false, don't go to default; otherwise go there
    -- TODO: for now, out of simplicity, we always join with default. This is safe but over-approximative
    (evalInstr rec (Wasm.Br def))

evalInstr _ (Wasm.I32Load memarg) = pop >>= load Wasm.I32 memarg >>= push
evalInstr _ (Wasm.I64Load memarg) = pop >>= load Wasm.I64 memarg >>= push
evalInstr _ (Wasm.F32Load memarg) = pop >>= load Wasm.F32 memarg >>= push
evalInstr _ (Wasm.F64Load memarg) = pop >>= load Wasm.F64 memarg >>= push
evalInstr _ (Wasm.I32Load8S memarg) = pop >>= load_ Wasm.I32 Size8 S memarg >>= push
evalInstr _ (Wasm.I32Load8U memarg) = pop >>= load_ Wasm.I32 Size8 U memarg >>= push
evalInstr _ (Wasm.I32Load16S memarg) = pop >>= load_ Wasm.I32 Size16 S memarg >>= push
evalInstr _ (Wasm.I32Load16U memarg) = pop >>= load_ Wasm.I32 Size16 U memarg >>= push
evalInstr _ (Wasm.I64Load8S memarg) = pop >>= load_ Wasm.I64 Size8 S memarg >>= push
evalInstr _ (Wasm.I64Load8U memarg) = pop >>= load_ Wasm.I64 Size8 U memarg >>= push
evalInstr _ (Wasm.I64Load16S memarg) = pop >>= load_ Wasm.I64 Size16 S memarg >>= push
evalInstr _ (Wasm.I64Load16U memarg) = pop >>= load_ Wasm.I64 Size16 U memarg >>= push
evalInstr _ (Wasm.I64Load32S memarg) = pop >>= load_ Wasm.I64 Size32 S memarg >>= push
evalInstr _ (Wasm.I64Load32U memarg) = pop >>= load_ Wasm.I64 Size32 U memarg >>= push
evalInstr _ (Wasm.I32Store memarg) = pop2 >>= store Wasm.I32 memarg
evalInstr _ (Wasm.I64Store memarg) = pop2 >>= store Wasm.I64 memarg
evalInstr _ (Wasm.F32Store memarg) = pop2 >>= store Wasm.F32 memarg
evalInstr _ (Wasm.F64Store memarg) = pop2 >>= store Wasm.F64 memarg
evalInstr _ (Wasm.I32Store8 memarg) = pop2 >>= store_ Wasm.I32 Size8 memarg
evalInstr _ (Wasm.I32Store16 memarg) = pop2 >>= store_ Wasm.I32 Size16 memarg
evalInstr _ (Wasm.I64Store8 memarg) = pop2 >>= store_ Wasm.I64 Size8 memarg
evalInstr _ (Wasm.I64Store16 memarg) = pop2 >>= store_ Wasm.I64 Size16 memarg
evalInstr _ (Wasm.I64Store32 memarg) = pop2 >>= store_ Wasm.I64 Size32 memarg
evalInstr rec (Wasm.Call f) = do
  fun <- getFunction f
  t <- getFunctionType fun
  let nParams = length (Wasm.params t)
  args <- reverse <$> mapM (const pop) [0..((length (Wasm.params t))-1)]
  res <- rec (Function f args)
  mapM_ push res
evalInstr rec (Wasm.If bt consequent alternative) = do
  v <- pop
  cond (return v) (rec (BlockBody bt consequent) >>= mapM_ push) (rec (BlockBody bt alternative) >>= mapM_ push)

evalInstr _ i = todo i

handleBreak :: WMonad m v => ([v] -> m ()) -> Esc m -> m ()
handleBreak onBreak b = mjoins (map (uncurry breakOrReturn) (getBreakLevelAndStack b))
  where breakOrReturn 0 stack = onBreak stack
        breakOrReturn level stack = escape (Break (level - 1) stack)

handleReturn :: WMonad m v => ([v] -> m ()) -> Esc m -> m ()
handleReturn onReturn b = trace "handleReturn" $ mjoins (map onReturn (getReturnStack b))
