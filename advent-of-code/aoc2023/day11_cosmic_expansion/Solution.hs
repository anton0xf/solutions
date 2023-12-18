{- --- Day 11: Cosmic Expansion --- https://adventofcode.com/2023/day/11 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Function ((&))
import Data.Ord
import Data.Bifunctor
import System.IO
import Text.Parsec hiding (space, spaces)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- data

type Loc = (Integer, Integer) -- (row, col), 0-based
type Bounds = (Loc, Loc) -- (top left corner, bottom right corner) inclusive

-- parsing

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

emptyP :: Parsec String u ()
emptyP = skipMany $ char '.'

sourceLoc :: SourcePos -> Loc
sourceLoc pos = (fromIntegral $ sourceLine pos - 1,
                 fromIntegral $ sourceColumn pos - 1)

starP :: Parsec String u Loc
starP = (sourceLoc <$> getPosition) <* char '#'

spaceMapP :: Parsec String u [Loc]
spaceMapP = concat <$> endBy1 (emptyP *> endBy starP emptyP) newline

parseIn :: String -> [Loc]
parseIn = tryParse spaceMapP

-- part 1

bounds :: [Loc] -> Bounds
bounds locs = let rows = map fst locs
                  cols = map snd locs
              in ((minimum rows, minimum cols),
                  (maximum rows, maximum cols))

-- return asc ordered list of empty rows' nums
emptyRows :: Bounds -> [Loc] -> [Integer]
emptyRows ((minRow, _), (maxRow, _)) locs = let
      rows = Set.fromList $ map fst locs
  in filter (not . (`Set.member` rows)) [minRow .. maxRow]

-- return asc ordered list of empty cols' nums
emptyCols :: Bounds -> [Loc] -> [Integer]
emptyCols ((_, minCol), (_, maxCol)) locs = let
      cols = Set.fromList $ map snd locs
  in filter (not . (`Set.member` cols)) [minCol .. maxCol]

-- asc ordered rows' nums -> locs -> new locs
expandEmptyRows :: [Integer] -> [Loc] -> [Loc]
expandEmptyRows rows locs = foldr (map . incGtRows) locs rows
  where incGtRows emptyRow loc@(row, col) = if row > emptyRow
          then (row + 1, col) else loc

-- asc ordered cols' nums -> locs -> new locs
expandEmptyCols :: [Integer] -> [Loc] -> [Loc]
expandEmptyCols cols locs = foldr (map . incGtCols) locs cols
  where incGtCols emptyCol loc@(row, col) = if col > emptyCol
          then (row, col + 1) else loc

expand :: Bounds -> [Loc] -> [Loc]
expand bounds locs = let
    rs = emptyRows bounds locs
    cs = emptyCols bounds locs
  in expandEmptyCols cs . expandEmptyRows rs $ locs

expand' :: [Loc] -> [Loc]
expand' locs = expand (bounds locs) locs

manhattan :: Loc -> Loc -> Integer
manhattan (r1, c1) (r2, c2) = fromIntegral $ abs (r2 - r1) + abs (c2 - c1)

-- get all 2-combinations of list
pairsOf :: [a] -> [(a, a)]
pairsOf [] = []
pairsOf (x : xs) = map (x,) xs ++ pairsOf xs

allDists :: [Loc] -> [Integer]
allDists = map (uncurry manhattan) . pairsOf

solve1 :: String -> Integer
solve1 = sum . allDists . expand' . parseIn

solution :: (String -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2

solve2 :: String -> Integer
solve2 _ = 0

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
