{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs)
import Language.Wasm as Wasm
import Data.ByteString.Lazy as LBS
import Control.Monad.IO.Class

loadFile :: MonadIO m => FilePath -> m (Either String Module)
loadFile = fmap Wasm.parse . (liftIO . LBS.readFile)

main :: IO ()
main = do
  fileName <- fmap head getArgs
  loaded <- loadFile fileName
  case loaded of
    Left err -> putStrLn err
    Right mod -> putStrLn "all good"
