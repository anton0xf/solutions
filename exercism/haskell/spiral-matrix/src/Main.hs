module Main (main) where

import Spiral (spiral)
import System.Environment

-- run it by `stack run 3` from parent directory
main :: IO ()
main = do
    args <- getArgs
    case args of
      [s] -> do
        let size = read s :: Int
        mapM_ (putStrLn . show) $ spiral size
      _ -> putStrLn "Usage: spiral size"
