{- --- Day 13: Point of Incidence --- https://adventofcode.com/2023/day/13 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Ord
import Data.Function
import Data.Functor
import Data.Bifunctor
import System.IO
import Text.Parsec hiding (space, spaces, State)
import Control.Applicative
import Control.Monad.List
import Control.Monad.State

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

dup :: a -> (a, a)
dup x = (x, x)

-- data
type Row = String
type Pattern = [Row]
type Size = (Int, Int) -- rows x columns

-- parsing

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

rowP :: Parsec String u Row
rowP = many1 (oneOf ".#")

patternP :: Parsec String u Pattern
patternP = endBy rowP newline

parseIn :: String -> [Pattern]
parseIn = tryParse (sepBy patternP newline)

-- part 1

-- get all not-empty splits with split index and reverted (to simplify isRefl) prefix
splits :: Row -> [(Int, (Row, Row))]
-- splits row = [(n, first reverse $ splitAt n row) | n <- [1 .. (length row - 1)]]
splits = iter 0 []
   where iter _ _ [] = []
         iter _ _ [_] = []
         iter n p (x : xs) = let n' = n + 1
                                 p' = x : p
           in (n', (p', xs)) : iter n' p' xs

isRefl :: (Row, Row) -> Bool
isRefl = and . uncurry (zipWith (==))

-- find reflexion columns
refl1 :: Row -> [Int]
refl1 = map fst . filter (isRefl . snd) . splits

refl :: Pattern -> [Int]
refl = map (fst . head) . filter (all (isRefl . snd)) . transpose . map splits

size :: Pattern -> Size
size p = (length p, length $ head p)

getRefls :: Pattern -> ([Int], [Int])
getRefls = bimap refl (refl . transpose) . dup

getSizeAndRefls :: Pattern -> (Size, ([Int], [Int]))
getSizeAndRefls = bimap size getRefls . dup

-- check input

checkIn :: IO ()
checkIn = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  let inp = map getSizeAndRefls $ parseIn input
  mapM_ print inp
  print $ "size: " ++ show ((minimum $ map (fst . fst) inp, maximum $ map (fst . fst) inp),
                            (minimum $ map (snd . fst) inp, maximum $ map (snd . fst) inp))
  print $ "all OK: " ++ show (all ((\(c, r) -> length (c ++ r) == 1) . snd) inp)
  hClose fh

-- solution 1

-- summarize pattern
sumPat :: [Int] -> [Int] -> Int
sumPat [n] [] = n
sumPat [] [n] = 100 * n

solve1 :: String -> Integer
solve1 = sum . map (fromIntegral . uncurry sumPat . getRefls) . parseIn

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
solve2 = undefined

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2

