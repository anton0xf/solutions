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

inEx :: [Char]
inEx = "#.##..##.\n"
    ++ "..#.##.#.\n"
    ++ "##......#\n"
    ++ "##......#\n"
    ++ "..#.##.#.\n"
    ++ "..##..##.\n"
    ++ "#.#.##.#.\n"
    ++ "\n"
    ++ "#...##..#\n"
    ++ "#....#..#\n"
    ++ "..##..###\n"
    ++ "#####.##.\n"
    ++ "#####.##.\n"
    ++ "..##..###\n"
    ++ "#....#..#\n"

patsEx :: [Pattern]
patsEx = [["#.##..##.",
           "..#.##.#.",
           "##......#",
           "##......#",
           "..#.##.#.",
           "..##..##.",
           "#.#.##.#."],
          ["#...##..#",
           "#....#..#",
           "..##..###",
           "#####.##.",
           "#####.##.",
           "..##..###",
           "#....#..#"]]

parseInTest :: Test
parseInTest = "parseIn" ~: parseIn inEx ~?= patsEx

splitsTest :: Test
splitsTest = "splits" ~: splits "##.#"
  ~?= [(1, ("#", "#.#")), (2, ("##", ".#")), (3, (".##", "#"))]

isReflTest :: Test
isReflTest = "isRefl" ~: test [
  isRefl ("#..", "#.") ~?= True,
  isRefl ("#.", "#.##") ~?= True,
  isRefl ("#.", ".##") ~?= False]

refl1Test :: Test
refl1Test = "refl1" ~: map refl1 (head patsEx)
  ~?= [[5, 7], [1, 5], [1, 5], [1, 5], [1, 5], [1, 3, 5, 7], [5]]

getSizeAndReflsTest :: Test
getSizeAndReflsTest = "getSizeAndRefls" ~: map getSizeAndRefls patsEx
  ~?= [((7, 9), ([5], [])), ((7, 9), ([], [4]))]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 405

tests1 :: Test
tests1 = "part 1" ~: test [parseInTest, splitsTest, isReflTest, refl1Test, getSizeAndReflsTest,
                           solve1Test]

-- part 2

tests2 :: Test
tests2 = "part 2" ~: test [True ~? "stub 2"]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
