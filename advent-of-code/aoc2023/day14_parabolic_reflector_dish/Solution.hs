{- --- Day 14: Parabolic Reflector Dish --- https://adventofcode.com/2023/day/14 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Ord
import Data.Function
import Data.Functor
import Data.Bifunctor
import System.IO
import GHC.Utils.Misc (count)
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

moveAllLeft :: Platform -> Platform
moveAllLeft = map moveLeft

-- solution 1
load :: Platform -> Integer
load p = let counts = map (fromIntegral . count (== 'O')) p
             n = fromIntegral $ length counts
         in sum $ zipWith (*) counts [n, (n-1) .. 1]

solve1 :: String -> Integer
solve1 = load . moveAllTop . parseIn

input :: IO String
input = readFile "input.txt"

solution :: (String -> Integer) -> IO ()
solution solve = input >>= print . solve

solution1 :: IO ()
solution1 = solution solve1

-- part 2

-- counter-clockwise rotation
rotate :: [[a]] -> [[a]]
rotate = foldr (zipWith (:) . reverse) (repeat [])

rotateClock :: [[a]] -> [[a]]
rotateClock [] = repeat []
rotateClock (xs : xss) = zipWith (++) (rotateClock xss) (map singleton xs)

{- cycle is combination of moving north, then west, then south, then east
   starting from west-to-left orientation -}
spinCycle :: Platform -> Platform
spinCycle = {- W -} rotateClock {- N -} . rotateClock
  . moveAllLeft {- E -} . rotateClock
  . moveAllLeft {- S -} . rotateClock
  . moveAllLeft {- W -} . rotateClock
  . moveAllLeft {- N -} . rotate {- W -}

loads200 :: IO [Integer]
loads200 = take 200 . map load . iterate spinCycle . parseIn <$> input
-- [101316,100329,100364,100494,100619,100689,100790,100915,100981,101085,101150,101218,101304,101387,101446,101511,101617,101692,101779,101847,101917,101955,102041,102074,102127,102179,102228,102280,102376,102457,102552,102646,102751,102841,102951,103036,103151,103255,103392,103498,103606,103702,103819,103922,104046,104142,104233,104311,104416,104503,104604,104693,104801,104854,104944,105026,105082,105136,105204,105242,105276,105312,105338,105343,105345,105371,105398,105421,105449,105479,105522,105538,105538,105531,105532,105516,105541,105561,105578,105571,105544,105500,105451,105422,105383,105367,105338,105331,105335,105338,105320,105286,105248,105229,105222,105199,105179,105164,105164,105174,105179,105184,105182,105169,105144,105107,105069,105011,104972,104930,104907,104873,104851,104819,104800,104773,104763,104749,104757,104753,104758,104753,104751,104729,104713,104698,104706,104711,104725,104725,104730,104721,104700,104669,104656,104643,104656,104660,104672,(start)104667,104663,104650,104649,104640,104651,104662,104671,104659,104654,104645,104644,104647,104666,(next)104667,104663,104650,104649,104640,104651,104662,104671,104659,104654,104645,104644,104647,104666,104667,104663,104650,104649,104640,104651,104662,104671,104659,104654,104645,104644,104647,104666,104667,104663,104650,104649,104640,104651,104662,104671,104659,104654,104645,104644,104647,104666,104667,104663,104650,104649,104640]
-- cycle starts at pos 139 and has length 14

detectCycle :: Ord a => [a] -> (Int, Int)
detectCycle xs = go 0 xs Map.empty where
  go n (x : xs) m = case Map.lookup x m of
    Nothing -> go (n + 1) xs (Map.insert x n m)
    Just start -> (start, n - start)

-- detectCycle . iterate spinCycle . parseIn <$> input == (139, 14)

{- some intuition:
λ> ("abcde" ++ cycle "fg") !! 100
'g'
λ> detectCycle ("abcde" ++ cycle "fg")
(5,2)
λ> (100 - 5) `mod` 2
1
λ> (!! 1) $ drop 5 ("abcde" ++ cycle "fg")
'g' -}

solve2 :: String -> Integer
solve2 str = let
      ps = iterate spinCycle $ parseIn str
      (start, len) = detectCycle ps
      pc = take len $ drop start ps
      n = 1000000000
      k = (n - start) `mod` len
  in load $ pc !! k

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2


