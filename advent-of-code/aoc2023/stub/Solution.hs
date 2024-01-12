{- --- Day ??: xxx --- https://adventofcode.com/2023/day/?? -}
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

input :: IO String
input = readFile "input.txt"

-- solution 1

solve1 :: String -> Integer
solve1 _ = 0 -- TODO

-- part 2

solve2 :: String -> Integer
solve2 _ = 0 -- TODO

-- main

applySolution :: (String -> Integer) -> IO ()
applySolution solve = input >>= print . solve

main :: IO ()
main = do
  putStr "Part 1: "
  applySolution solve1
  putStr "Part 2: "
  applySolution solve2


