{- --- Day 6: Wait For It --- https://adventofcode.com/2023/day/6 -}
{- install dependency:
$ cabal install --lib parsec -}
module Solution where

import Data.Function ((&))
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
waysToWin (Race t d) = if t^2 < 4*d then 0
  else let
      discr = fromIntegral $ t^2 - 4*d :: Double
      w = sqrt discr
      t1 = max 0 $ floor $ (fromIntegral t - w) / 2 + 1
      t2 = min t $ ceiling $ (fromIntegral t + w) / 2 - 1
  in if t1 > t then 0
  else t2 - t1 + 1

solve1 :: [Race] -> Integer
solve1 = product . map waysToWin

solution1 :: IO ()
solution1 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve1 $ parseInput input
  hClose fh

-- part 2

bigIntP :: Parsec String u Integer
bigIntP = read <$> many1 (digit <* spaces)

bigRaceP :: Parsec String u Race
bigRaceP = Race <$> (string "Time:" *> spaces *> bigIntP <* newline)
  <*> (string "Distance:" *> spaces *> bigIntP <* newline)

parseInput2 :: String -> Race
parseInput2 = tryParse bigRaceP

solve2 :: Race -> Integer
solve2 = waysToWin

solution2 :: IO ()
solution2 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve2 $ parseInput2 input
  hClose fh

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
