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

inEx :: String
inEx = "...#......\n"
    ++ ".......#..\n"
    ++ "#.........\n"
    ++ "..........\n"
    ++ "......#...\n"
    ++ ".#........\n"
    ++ ".........#\n"
    ++ "..........\n"
    ++ ".......#..\n"
    ++ "#...#.....\n"

locsEx :: [Loc]
locsEx = [(0, 3), (1, 7), (2, 0), (4, 6), (5, 1), (6, 9), (8, 7), (9, 0), (9, 4)]

boundsEx :: Bounds
boundsEx = ((0, 0), (9, 9))

emptyRowsEx :: [Integer]
emptyRowsEx = [3, 7]

emptyColsEx :: [Integer]
emptyColsEx = [2, 5, 8]

locsEREx :: [Loc]
locsEREx = [(0, 3), (1, 7), (2, 0), (5, 6), (6, 1), (7, 9), (10, 7), (11, 0), (11, 4)]

locsEEx :: [Loc]
locsEEx = [(0, 4), (1, 9), (2, 0), (5, 8), (6, 1), (7, 12), (10, 9), (11, 0), (11, 5)]

parseInTest :: Test
parseInTest = "parseIn" ~: parseIn inEx ~?= locsEx

boundsTest :: Test
boundsTest = "bounds" ~: bounds locsEx ~?= boundsEx

emptyRowsTest :: Test
emptyRowsTest = "emptyRows" ~: emptyRows boundsEx locsEx ~?= emptyRowsEx

emptyColsTest :: Test
emptyColsTest = "emptyCols" ~: emptyCols boundsEx locsEx ~?= emptyColsEx

expandEmptyRowsTest :: Test
expandEmptyRowsTest = "expandEmptyRows" ~: expandEmptyRows emptyRowsEx locsEx ~?= locsEREx

expandEmptyColsTest :: Test
expandEmptyColsTest = "expandEmptyCols" ~: expandEmptyCols emptyColsEx locsEREx ~?= locsEEx

expandTest :: Test
expandTest = "expand" ~: expand boundsEx locsEx ~?= locsEEx

manhattanTest :: Test
manhattanTest = "manhattan" ~: manhattan (6, 1) (11, 5) ~?= 9

pairsOfTest :: Test
pairsOfTest = "pairsOf" ~: pairsOf [1, 2, 3] ~?= [(1, 2), (1, 3), (2, 3)]

allDistsTest :: Test
allDistsTest = "allDists" ~: allDists locsEEx
  ~?= [6,6,9,9,15,15,15,12,10,5,13,9,9,19,14,11,5,17,17,9,14,8,6,6,14,9,12,12,6,9,6,16,11,10,5,5]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 374

tests1 :: Test
tests1 = "part 1" ~: test [
  parseInTest, boundsTest,
  emptyRowsTest, emptyColsTest, expandEmptyRowsTest, expandEmptyColsTest, expandTest,
  manhattanTest, pairsOfTest, allDistsTest, solve1Test]

-- part 2

tests2 :: Test
tests2 = "part 2" ~: test [True ~? "stub"]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
