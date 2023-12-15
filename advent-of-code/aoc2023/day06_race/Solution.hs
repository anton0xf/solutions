{- --- Day 6: Wait For It --- https://adventofcode.com/2023/day/6 -}
{- install dependency:
$ cabal install --lib parsec -}
module Solution where

import Data.Maybe
import Data.Either
import Data.List
import Data.Function ((&))
import Control.Monad
import System.IO
import Text.Parsec hiding (space, spaces)

data Races = Races { times :: [Integer], distances :: [Integer] }
  deriving (Show, Eq)

data Race = Race { time :: Integer, dist :: Integer }
  deriving (Show, Eq)

-- parsing
space :: Parsec String u Char
space = char ' '

spaces :: Parsec String u String
spaces = many space

intP :: Parsec String u Integer
intP = read <$> many1 digit

intsP :: Parsec String u [Integer]
intsP = spaces *> sepEndBy1 intP spaces

racesP :: Parsec String u Races
racesP = Races <$> (string "Time:" *> spaces *> intsP <* newline)
  <*> (string "Distance:" *> spaces *> intsP <* newline)

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

convRaces :: Races -> [Race]
convRaces (Races ts ds) = zipWith Race ts ds

parseInput :: String -> [Race]
parseInput = convRaces . tryParse racesP

-- part 1

-- raceTime -> pushTime -> distance
timesToDist :: Integer -> Integer -> Integer
timesToDist rt t = if t >= rt then 0 else t * (rt - t)

waysToWin :: Race -> Integer
waysToWin (Race t d) = [0 .. t] & map (timesToDist t)
  & filter (> d) & length & fromIntegral

solve1 :: [Race] -> Integer
solve1 = product . map waysToWin

solution :: ([Race] -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseInput input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
