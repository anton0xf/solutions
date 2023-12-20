module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import Text.Parsec hiding (space, spaces)
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple
import Data.Maybe

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- part 1

inEx :: String
inEx = "???.### 1,1,3\n"
    ++ ".??..??...?##. 1,1,3\n"
    ++ "?#?#?#?#?#?#?#? 1,3,1,6\n"
    ++ "????.#...#... 4,1,1\n"
    ++ "????.######..#####. 1,6,5\n"
    ++ "?###???????? 3,2,1\n"

rowsEx :: [Row]
rowsEx = [Row "???.###" [1, 1, 3],
          Row ".??..??...?##." [1, 1, 3],
          Row "?#?#?#?#?#?#?#?" [1, 3, 1, 6],
          Row "????.#...#..." [4, 1, 1],
          Row "????.######..#####." [1, 6, 5],
          Row "?###????????" [3, 2, 1]]

parseInTest :: Test
parseInTest = "parseIn" ~: parseIn inEx ~?= rowsEx

tryGetGroupTest :: Test
tryGetGroupTest = "tryGetGroup" ~: test [
  tryGetGroup "#?#.." 3 ~?= Just ("###", "..") ]

arrsTest :: Test
arrsTest = "arrs" ~: test [
  arrs "." (Row "" []) ~?= ["."],
  arrs "" (Row "." []) ~?= ["."],
  arrs "" (Row "#" [1]) ~?= ["#"],
  arrs "" (Row "?" [1]) ~?= ["#"],
  arrs "" (Row "##" [1]) ~?= [],
  arrs "" (Row "##" [2]) ~?= ["##"],
  arrs "" (Row "#.#" [2]) ~?= []]

tests1 :: Test
tests1 = "part 1" ~: test [parseInTest, tryGetGroupTest, arrsTest]

-- part 2

tests2 :: Test
tests2 = "part 2" ~: test [True ~? "stub"]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
