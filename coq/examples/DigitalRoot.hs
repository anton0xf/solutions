module DigitalRoot where
import Data.List.Split (chunksOf)

digits :: Integer -> [Integer]
digits n | n <= 9 = [n]
digits n = (n `mod` 10) : digits (n `div` 10)

-- digits 1234 = [4,3,2,1]

root :: Integer -> Integer
root n = let s = sum $ digits n
         in if s < 10 then s else root s

pows2 :: [Integer]
pows2 = iterate (* 2) 2

rootsChunks :: [[Integer]]
rootsChunks = chunksOf 6 $ map root pows2

-- head rootsChunks = [2,4,8,7,5,1]

allEq :: (Eq a) => [a] -> Bool
allEq (x : xs) = all (== x) xs

-- test that they are really equal
allTheSame :: Bool
allTheSame = allEq $ take 100 rootsChunks
