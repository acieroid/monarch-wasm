{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs)
import Language.Wasm as Wasm
import qualified Data.ByteString.Lazy as LBS
import Control.Monad.IO.Class
import Analysis.WebAssembly.Fixpoint (analyze, WasmCmp, WasmRes)
import Data.Map (Map)
import Analysis.WebAssembly.Domain (ConstPropValue, SingleAddress)

loadFile :: MonadIO m => FilePath -> m (Either String Module)
loadFile = fmap Wasm.parse . (liftIO . LBS.readFile)

run :: Module -> (Map (WasmCmp ConstPropValue) (WasmRes ConstPropValue), Map SingleAddress ConstPropValue)
run = analyze

main :: IO ()
main = do
  fileName <- fmap head getArgs
  loaded <- loadFile fileName
  case loaded of
    Left err -> putStrLn err
    Right m -> do
      let (returns, store) = run m
      putStrLn "Return values:"
      print returns
