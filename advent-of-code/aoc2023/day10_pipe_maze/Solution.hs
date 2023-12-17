{- --- Day 10: Pipe Maze --- https://adventofcode.com/2023/day/10 -}
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

type Loc = (Int, Int) -- (row, col), 0-based

data Maze = Maze { start :: Loc, pipes :: Map Loc Char }
  deriving (Show, Eq)

isPipe :: Char -> Bool
isPipe = (`elem` "|-LJ7FS")

isStart :: Char -> Bool
isStart = (== 'S')

-- parsing

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

mazeCharP :: Parsec String u Char
mazeCharP = oneOf "|-LJ7F.S"

mazeP :: Parsec String u [String]
mazeP = endBy1 (many1 mazeCharP) newline

convMaze :: [String] -> Maze
convMaze css = let
      convRow row = zipWith ((,) . (row,)) [0..]
      locs = concat $ zipWith convRow [0..] css
      pipes = filter (isPipe . snd) locs
      start = fromJust $ find (isStart . snd) pipes
  in Maze (fst start) (Map.fromList pipes)

parseIn :: String -> Maze
parseIn = convMaze . tryParse mazeP

-- part 1

data Dir = U | R | D | L
  deriving (Show, Eq)

dirs :: [Dir]
dirs = [U, R, D, L]

invDir :: Dir -> Dir
invDir U = D
invDir R = L
invDir D = U
invDir L = R

charDirs :: Char -> [Dir]
charDirs '|' = [U, D]
charDirs '-' = [L, R]
charDirs 'L' = [U, R]
charDirs 'J' = [U, L]
charDirs '7' = [L, D]
charDirs 'F' = [R, D]
charDirs 'S' = dirs

move :: Loc -> Dir -> Loc
move (row, col) U = (row - 1, col)
move (row, col) R = (row, col + 1)
move (row, col) D = (row + 1, col)
move (row, col) L = (row, col - 1)

neighbours :: Loc -> [(Dir, Loc)]
neighbours loc = map (\dir -> (dir, move loc dir)) dirs

adjInDir :: Map Loc Char -> Loc -> Dir -> Maybe Loc
adjInDir m loc dir = do
      let nloc = move loc dir
      nchar <- Map.lookup nloc m
      if invDir dir `elem` charDirs nchar
        then Just nloc else Nothing

adj :: Map Loc Char -> Loc -> [Loc]
adj m loc = mapMaybe (adjInDir m loc) (charDirs $ m ! loc)

bfsi :: Map Loc Char -> (Set Loc, Set Loc) -> (Set Loc, Set Loc)
bfsi m (visited, q) = let
      visited' = Set.union visited q
      adjs = Set.fromList (concatMap (adj m) q) \\ visited'
  in (visited', adjs)

bfs :: Map Loc Char -> Integer -> Set Loc -> Set Loc -> Integer
bfs m n visited q = let
      visited' = Set.union visited q
      adjs = Set.fromList (concatMap (adj m) q) \\ visited'
  in if Set.null adjs then n
     else bfs m (n + 1) visited' adjs

solve1 :: Maze -> Integer
solve1 (Maze start m) = bfs m 0 Set.empty (Set.singleton start)

solution :: (Maze -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseIn input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2
solve2 :: Maze -> Integer
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
