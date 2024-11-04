{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs)
import Language.Wasm as Wasm
import qualified Data.ByteString.Lazy as LBS
import Control.Monad.IO.Class
import Analysis.WebAssembly.Fixpoint (analyze, WasmCmp, WasmRes)
import qualified Data.Map as M
import Analysis.WebAssembly.Domain (ConstPropValue)
import Analysis.WebAssembly.Semantics (WasmBody(..))

loadFile :: MonadIO m => FilePath -> m (Either String Module)
loadFile = fmap Wasm.parse . (liftIO . LBS.readFile)

run :: Module -> (M.Map (WasmCmp ConstPropValue) (WasmRes ConstPropValue), M.Map ConstPropValue ConstPropValue)
run = analyze

main :: IO ()
main = do
  fileName <- fmap head getArgs
  loaded <- loadFile fileName
  case loaded of
    Left err -> putStrLn err
    Right m -> do
      let (returns, _store) = run m
      putStrLn "Return values:"
      mapM_ (\(k, v) -> case k of
                (EntryFunction idx, ()) -> putStrLn $ show idx ++ ": " ++ show v
                _ -> return ())
        (M.assocs returns)
