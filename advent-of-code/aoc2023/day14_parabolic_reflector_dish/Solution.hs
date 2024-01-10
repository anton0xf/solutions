{- --- Day 14: Parabolic Reflector Dish --- https://adventofcode.com/2023/day/14 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Ord
import Data.Function
import Data.Functor
import Data.Bifunctor
import System.IO
import GHC.Utils.Misc
import Text.Parsec hiding (space, spaces, State, count)
import Control.Applicative
import Control.Monad.List
import Control.Monad.State

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- data
type Row = String
type Platform = [Row]

-- parsing

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

rowP :: Parsec String u Row
rowP = many1 (oneOf "O#.")

parseIn :: String -> Platform
parseIn = tryParse (endBy rowP newline)

-- part 1
moveLeft :: Row -> Row
moveLeft = concat . move . group
  where move (xs1@('.' : _) : xs2@('O' : _) : xss) = xs2 : move (xs1 : xss)
        move (xs1@('.' : _) : xs2@('.' : _) : xss) = move $ (xs1 ++ xs2) : xss
        move (xs1 : xs2 : xss) = xs1 : move (xs2 : xss)
        move xss = xss

moveAllTop :: Platform -> Platform
moveAllTop = transpose . map moveLeft . transpose

-- solution 1
load :: Platform -> Integer
load p = let counts = map (fromIntegral . count (== 'O')) p
             n = fromIntegral $ length counts
         in sum $ zipWith (*) counts [n, (n-1) .. 1]

solve1 :: String -> Integer
solve1 = load . moveAllTop . parseIn

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
solve2 = undefined . parseIn

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2


