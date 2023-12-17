{- --- Day 9: Mirage Maintenance --- https://adventofcode.com/2023/day/9 -}
module Solution where

import Data.Maybe
import Data.List
import Data.Function ((&))
import Data.Ord
import Data.Bifunctor
import System.IO
import Text.Parsec hiding (space, spaces)

import Data.Map (Map)
import qualified Data.Map as Map

-- parsing
tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

space :: Parsec String u Char
space = char ' '

intP :: Parsec String u Integer
intP = read <$> ((++) <$> option "" (string "-") <*> many1 digit)

intsP :: Parsec String u [Integer]
intsP = sepBy1 intP space

parseIn :: String -> [[Integer]]
parseIn = tryParse $ endBy1 intsP newline

-- part 1
diffs :: [Integer] -> [Integer]
diffs xs = zipWith (-) (tail xs) xs

allZeros :: [Integer] -> Bool
allZeros = all (== 0)

allDiffs :: [Integer] -> [[Integer]]
allDiffs xs = takeWhile (not . allZeros) $ iterate diffs xs

nextInt :: [Integer] -> Integer
nextInt = sum . map last . allDiffs

solve1 :: [[Integer]] -> Integer
solve1 = sum . map nextInt

solution :: ([[Integer]] -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseIn input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  -- putStr "Part 2: "
  -- solution2
