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

arrscTest :: Test
arrscTest = "arrsc" ~: test [
  arrsc False (CRow [] [1]) ~?= [],
  arrsc True (CRow [('.', 1)] []) ~?= [[('.', 1)]],
  arrsc False (CRow [('.', 1)] []) ~?= [[('.', 1)]],
  arrsc True (CRow [('#', 1)] [1]) ~?= [[('#', 1)]],
  arrsc False (CRow [('#', 1)] [1]) ~?= [],
  arrsc True (CRow [('#', 2)] [1]) ~?= [],
  arrsc True (CRow [('#', 1)] [2]) ~?= [],
  arrsc True (CRow [('#', 2)] [2]) ~?= [[('#', 2)]],
  arrsc True (CRow [('#', 1), ('.', 1), ('#', 1)] [1, 1]) ~?= [[('#', 1), ('.', 1), ('#', 1)]],
  arrsc False (CRow [('#', 1), ('.', 1), ('#', 1)] [1, 1]) ~?= [],
  arrsc True (CRow [('#', 1), ('.', 1), ('#', 1)] [1]) ~?= [],
  arrsc True (CRow [('#', 1), ('.', 1), ('#', 1)] [2]) ~?= [],
  arrsc True (CRow [('?', 1)] [1]) ~?= [[('#', 1)]],
  arrsc False (CRow [('?', 1)] [1]) ~?= [],
  arrsc False (CRow [('?',1)] []) ~?= [[('.', 1)]],
  arrsc True (CRow [('?', 1)] [2]) ~?= [],
  arrsc True (CRow [('?', 2)] [1]) ~?= [[('#', 1), ('.', 1)], [('.', 1), ('#', 1)]],
  arrsc False (CRow [('?', 2)] [1]) ~?= [[('.', 1), ('#', 1)]],
  arrsc True (CRow [('?', 3)] [1, 1]) ~?= [[('#',1),('.',1),('#',1)]],
  arrsc False (CRow [('?', 3)] [1, 1]) ~?= [],
  arrsc False (CRow [('?', 1), ('.', 1), ('#', 1)] [1]) ~?= [[('.', 1), ('.', 1), ('#', 1)]],
  un (arrsc True (comp $ Row "??.#" [1, 1])) ~?= ["#..#", ".#.#"],
  "all ex" ~: map (length . arrsc True . compressRow) rowsEx ~?= [1, 4, 1, 1, 4, 10]]
  where comp = compressRow
        un = map uncompressNChs

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 21

tests1 :: Test
tests1 = "part 1" ~: test [parseInTest, arrscTest, solve1Test]

-- part 2

arrs2Test :: Test
arrs2Test = "arrs2" ~: test [
  "full ex" ~: map (length . arrs2) rowsEx ~?= [1, 16384, 1, 16, 2500, 506250]]

solve2Test :: Test
solve2Test = "solve2" ~: solve2 inEx ~?= 525152

tests2 :: Test
tests2 = "part 2" ~: test [arrs2Test, solve2Test]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure

{-
-- unoptimized time:
$ time runghc Test.hs
> Cases: 12  Tried: 12  Errors: 0  Failures: 0
> runghc Test.hs  54,40s user 0,11s system 100% cpu 54,391 total

-- using arrsc
$ time runghc Test.hs
> Cases: 35  Tried: 35  Errors: 0  Failures: 0
> runghc Test.hs  8,37s user 0,23s system 100% cpu 8,582 total
-}
