module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple
import Data.Maybe

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

mazeInEx1 :: String
mazeInEx1 = ".....\n"
         ++ ".S-7.\n"
         ++ ".|.|.\n"
         ++ ".L-J.\n"
         ++ ".....\n"

mazeEx1 :: Maze
mazeEx1 = Maze { start = (1,1),
                 pipes = Map.fromList [
                   ((1, 1), 'S'), ((1, 2), '-'), ((1, 3), '7'),
                   ((2, 1), '|'), ((2, 3), '|'),
                   ((3, 1), 'L'), ((3, 2), '-'), ((3, 3), 'J')]}

parseInTest :: Test
parseInTest = "parseIn" ~: convMaze (parseIn mazeInEx1) ~?= mazeEx1

adjTest :: Test
adjTest = "adj" ~: test [
    adj m (1,1) ~?= [(1,2),(2,1)],
    adj m (1,2) ~?= [(1,1),(1,3)],
    adj m (1,3) ~?= [(1,2),(2,3)],
    adj m (2,1) ~?= [(1,1),(3,1)],
    adj m (2,3) ~?= [(1,3),(3,3)],
    adj m (3,1) ~?= [(2,1),(3,2)],
    adj m (3,2) ~?= [(3,1),(3,3)],
    adj m (3,3) ~?= [(2,3),(3,2)]]
  where m = pipes mazeEx1

bfsiTest :: Test
bfsiTest = "bfsi" ~: let (Maze start m) = mazeEx1
  in (iterate (bfsi m) (Set.empty, Set.singleton start) & map snd & take 6)
     ~?= [Set.fromList [(1,1)],
          Set.fromList [(1,2),(2,1)],
          Set.fromList [(1,3),(3,1)],
          Set.fromList [(2,3),(3,2)],
          Set.fromList [(3,3)],
          Set.fromList []]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 (parseIn mazeInEx1) ~?= 4

tests1 :: Test
tests1 = "part 1" ~: test [parseInTest, adjTest, bfsiTest, solve1Test]

-- part 2

mazeInEx2 :: String
mazeInEx2 = "...........\n"
         ++ ".S-------7.\n"
         ++ ".|F-----7|.\n"
         ++ ".||.....||.\n"
         ++ ".||.....||.\n"
         ++ ".|L-7.F-J|.\n"
         ++ ".|..|.|..|.\n"
         ++ ".L--J.L--J.\n"
         ++ "...........\n"

tests2 :: Test
tests2 = "part 2" ~: test [solve2 (parseIn mazeInEx2) ~?= 4]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
