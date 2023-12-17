module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple

inEx :: String
inEx = "0 3 6 9 12 15\n"
    ++ "1 3 6 10 15 21\n"
    ++ "10 13 16 21 30 45\n"

intsEx :: [[Integer]]
intsEx = [[0, 3, 6, 9, 12, 15],
          [1, 3, 6, 10, 15, 21],
          [10, 13, 16, 21, 30, 45]]

intPTest :: Test
intPTest = "intP" ~: test [
  tryParse intP "12" ~?= 12,
  tryParse intP "-13" ~?= -13]

parseInTest :: Test
parseInTest = "parseIn" ~: parseIn inEx ~?= intsEx

diffsTest :: Test
diffsTest = "diffs" ~: map diffs intsEx
  ~?= [[3, 3, 3, 3, 3],
       [2, 3, 4, 5, 6],
       [3, 3, 5, 9, 15]]

allDiffsTest :: Test
allDiffsTest = "allDiffs" ~: allDiffs [10, 13, 16, 21, 30, 45]
  ~?= [[10, 13, 16, 21, 30, 45],
       [3, 3, 5, 9, 15],
       [0, 2, 4, 6],
       [2, 2, 2]]

nextIntTest :: Test
nextIntTest = "nextInt" ~: map nextInt intsEx ~?= [18, 28, 68]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 intsEx ~?= 114

tests1 :: Test
tests1 = "part 1" ~: test [intPTest, parseInTest, diffsTest, allDiffsTest, nextIntTest, solve1Test]

tests2 :: Test
tests2 = "part 2" ~: test [True ~? "stub"]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
