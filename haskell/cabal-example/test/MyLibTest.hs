module Main (main) where

import MyLib
import System.Exit

main :: IO ()
main = do
  putStrLn "MyLibTest: run"
  if take 5 (map fib [1..]) == [1, 1, 2, 3, 5]
  then exitSuccess else exitFailure
