-- <4 kyu> Next bigger number with the same digits
-- https://www.codewars.com/kata/55983863da40caa2c900004e
module NextBigger (nextBigger) where

import Data.List ( sort )

-- get digits of number LE (from little to big powers of 10)
digits :: Int -> [Int]
digits 0 = []
digits n = mod n 10 : digits (div n 10)

-- digits 1243
-- => [3,4,2,1]

-- split by first inversion
-- digits LE -> little accumulator -> (little reverted, big)
splitByFirstInv :: [Int] -> ([Int], [Int])
splitByFirstInv digits =
  let split [] ys = (ys, [])
      split [x] ys = (x:ys, [])
      split (x1 : x2 : xs) ys = if x1 <= x2
        then split (x2 : xs) (x1 : ys)
        else (x1 : ys, x2 : xs)
  in split digits []

-- splitByFirstInv (digits 12654) []
-- => ([6,5,4],[2,1])

-- digits LE -> number
num :: [Int] -> Int
num [] = 0
num (x : xs) = x + 10 * num xs

-- n -> digits -> (digit, digits)
-- remove and get minimal digit > n
-- digits shlould be sorted
removeNext :: Int -> [Int] -> (Int, [Int])
removeNext d digits =
  let remove n (x:xs) acc =
        if n < x then (x, acc ++ xs)
        else remove n xs (x:acc)
  in remove d digits []

-- removeNext 2 [1,3,4]
-- => (3,[1,4])

-- minumim number (which could be made by permutation of `digits n`) greater than n
nextBigger :: Int -> Int 
nextBigger n =
  let (xs, ys) = splitByFirstInv (digits n)
      sorted_xs = sort xs
  in case ys of
    [] -> -1
    y : ys' -> let (x, xs') = removeNext y sorted_xs
               in num $ reverse (sort $ y : xs') ++ (x : ys')

-- nextBigger 132
-- => 213
