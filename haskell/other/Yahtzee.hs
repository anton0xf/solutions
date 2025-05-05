-- https://www.carlopescio.com/2011/06/cut-red-wire.html
module Yahtzee where

import Data.Map ((!), fromList, Map)
import Data.List (concat, reverse, filter, group, sort, sortBy, take)

type Category = String
type Rules = Map Category ([Int] -> Int)

score :: Rules -> Category -> [Int] -> Int
score rules category dices = (rules ! category) (sort dices)

scoreKata :: Category -> [Int] -> Int
scoreKata = score kataRules

-- https://codingdojo.org/kata/Yahtzee/
kataRules :: Rules
kataRules = fromList [
  ("ones", sumOf 1),
  ("twos", sumOf 2),
  ("threes", sumOf 3),
  ("fours", sumOf 4),
  ("fives", sumOf 5),
  ("sixes", sumOf 6),
  ("pair", pair),
  ("two pairs", twoPairs),
  ("three of a kind", nOfAKind 3),
  ("four of a kind", nOfAKind 4),
  ("small straight", \ds -> if ds == [1..5] then 15 else 0),
  ("large straight", \ds -> if ds == [2..6] then 20 else 0),
  ("full house", fullHouse),
  ("yahtzee", yahtzee),
  ("chance", sum)
  ]

sumOf :: Int -> [Int] -> Int
sumOf n = sum . filter (== n)

nths :: Int -> [Int] -> [[Int]]
nths n = filter ((== n) . length) . group

pair :: [Int] -> Int
pair ds = case nths 2 (reverse ds) of
  (p:_) -> sum p
  _ -> 0

twoPairs :: [Int] -> Int
twoPairs ds = case nths 2 ds of
  (p1 : p2 : _) -> sum $ p1 ++ p2
  _ -> 0

nOfAKind :: Int -> [Int] -> Int
nOfAKind n = sum . concat . nths n

fullHouse :: [Int] -> Int
fullHouse ds =
  let pairs = nths 2 ds
      triples = nths 3 ds
  in case (pairs, triples) of
    (_:_, _:_) -> sum . concat $ pairs ++ triples
    _ -> 0

yahtzee :: [Int] -> Int
yahtzee ds = case nths 5 ds of
  (g:_) -> 50
  _ -> 0

test :: Bool
test =
  scoreKata "fours" [1, 1, 2, 4, 4] == 8 &&
  scoreKata "pair" [3, 3, 3, 4, 4] == 8 &&
  scoreKata "two pairs" [1, 1, 2, 3, 3] == 8 &&
  scoreKata "three of a kind" [3, 3, 3, 4, 5] == 9 &&
  scoreKata "full house" [1, 1, 2, 2, 2] == 8 &&
  scoreKata "full house" [4, 4, 4, 4, 4] == 0 &&
  True
