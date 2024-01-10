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

rotateTest :: Test
rotateTest = "rotate" ~: test [
  rotate [[1, 2], [3, 4]] ~?= [[2, 4], [1, 3]],
  rotate [[1, 2]] ~?= [[2], [1]],
  rotate [[2],[1]] ~?= [[2, 1]]]

rotateClockTest :: Test
rotateClockTest = "rotateClock" ~: test [
  rotateClock [[1, 2]] ~?= [[1], [2]],
  rotateClock [[2, 4], [1, 3]] ~?= [[1, 2], [3, 4]]]

spinCycleTest :: Test
spinCycleTest = "spinCycle" ~: test [
  spinCycle platformEx
    ~?= [".....#....",
         "....#...O#",
         "...OO##...",
         ".OO#......",
         ".....OOO#.",
         ".O#...O#.#",
         "....O#....",
         "......OOOO",
         "#...O###..",
         "#..OO#...."],
  spinCycle (spinCycle platformEx)
    ~?= [".....#....",
         "....#...O#",
         ".....##...",
         "..O#......",
         ".....OOO#.",
         ".O#...O#.#",
         "....O#...O",
         ".......OOO",
         "#..OO###..",
         "#.OOO#...O"],
  spinCycle (spinCycle $ spinCycle platformEx)
    ~?= [".....#....",
         "....#...O#",
         ".....##...",
         "..O#......",
         ".....OOO#.",
         ".O#...O#.#",
         "....O#...O",
         ".......OOO",
         "#...O###.O",
         "#.OOO#...O"]]

solve2Test :: Test
solve2Test = "solve2" ~: solve2 inEx ~?= 64

tests2 :: Test
tests2 = "part 2" ~: test [rotateTest, rotateClockTest, spinCycleTest, solve2Test]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
