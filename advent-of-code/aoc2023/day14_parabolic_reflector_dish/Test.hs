module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import GHC.Utils.Misc
import Text.Parsec hiding (space, spaces, count)
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
inEx = "O....#....\n"
    ++ "O.OO#....#\n"
    ++ ".....##...\n"
    ++ "OO.#O....O\n"
    ++ ".O.....O#.\n"
    ++ "O.#..O.#.#\n"
    ++ "..O..#O..O\n"
    ++ ".......O..\n"
    ++ "#....###..\n"
    ++ "#OO..#....\n"

platformEx :: Platform
platformEx = ["O....#....",
              "O.OO#....#",
              ".....##...",
              "OO.#O....O",
              ".O.....O#.",
              "O.#..O.#.#",
              "..O..#O..O",
              ".......O..",
              "#....###..",
              "#OO..#...."]

parseInTest :: Test
parseInTest = "parseIn" ~: parseIn inEx ~?= platformEx

moveLeftTest :: Test
moveLeftTest = "moveLeft" ~: test [
  moveLeft ".OO..#O...O." ~?= "OO...#OO....",
  moveLeft ".OO..O" ~?= "OOO..."]

platfromExMovedTop :: Platform
platfromExMovedTop = ["OOOO.#.O..",
                      "OO..#....#",
                      "OO..O##..O",
                      "O..#.OO...",
                      "........#.",
                      "..#....#.#",
                      "..O..#.O.O",
                      "..O.......",
                      "#....###..",
                      "#....#...."]

moveAllTopTest :: Test
moveAllTopTest = "moveAllTop" ~: moveAllTop platformEx ~?= platfromExMovedTop

loadTest :: Test
loadTest = "load" ~: load platfromExMovedTop ~?= 136

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 136

tests1 :: Test
tests1 = "part 1" ~: test [parseInTest, moveLeftTest, moveAllTopTest, loadTest, solve1Test]

-- part 2

tests2 :: Test
tests2 = "part 2" ~: True ~? "stub" -- solve2 inEx ~?= ?

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
