module Main (main) where

import MyLib
import System.Exit
import Test.HUnit

testFib = TestCase (assertEqual "first five fibs"
                    [1, 1, 2, 3, 5]
                    (take 5 (map fib [1..])))

testSet = [testFib]

main :: IO ()
main = do
  counts <- runTestTT (test testSet)
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
