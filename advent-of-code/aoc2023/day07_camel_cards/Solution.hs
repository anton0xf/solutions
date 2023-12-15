{- --- Day 7: Camel Cards --- https://adventofcode.com/2023/day/7 -}
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
space :: Parsec String u Char
space = char ' '

handP :: Parsec String u String
handP = many1 alphaNum

intP :: Parsec String u Integer
intP = read <$> many1 digit

lineP :: Parsec String u (String, Integer)
lineP = (,) <$> (handP <* space) <*> intP

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

parseInput :: String -> [(String, Integer)]
parseInput = tryParse (endBy lineP newline)

-- common

cards :: [Char]
cards = "AKQJT98765432"

data Type = Five | Four | FullHouse | Three | TwoPair | Pair | High
  deriving (Show, Eq, Ord)

types :: [Type]
types = [Five, Four, FullHouse, Three, TwoPair, Pair, High]

data Hand = Hand { typ :: Type, str :: String }
  deriving (Eq, Show)

cardIds :: Map Char Int
cardIds = Map.fromList $ zip cards [1..]

cardId :: Char -> Int
cardId card = Map.lookup card cardIds & fromJust

handOrd :: Hand -> Down (Type, [Int])
handOrd h = Down (typ h, map cardId $ str h)

instance Ord Hand where
  compare :: Hand -> Hand -> Ordering
  compare x y = compare (handOrd x) (handOrd y)

countCards :: String -> Map Char Int
countCards = foldl add Map.empty
  where add m card = Map.insertWith (+) card 1 m

cardCounts :: String -> [Int]
cardCounts h = countCards h & Map.elems & sortOn Down

countsType :: [Int] -> Type
countsType (5 : _)     = Five
countsType (4 : _)     = Four
countsType (3 : 2 : _) = FullHouse
countsType (3 : _)     = Three
countsType (2 : 2 : _) = TwoPair
countsType (2 : _)     = Pair
countsType _           = High

handType :: String -> Type
handType = countsType . cardCounts

toHand :: String -> Hand
toHand s = Hand (handType s) s

-- part 1

-- [(hand str, bid)] -> [(rank, hand, bid)]
rankBids :: [(String, Integer)] -> [(Integer, (Hand, Integer))]
rankBids bids = bids & map (first toHand) & sortOn fst & zip [1..]

solve1 :: [(String, Integer)] -> Integer
solve1 = sum . map (uncurry (*) . second snd) . rankBids

solution :: ([(String, Integer)] -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseInput input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2

cardId2 :: Char -> Int
cardId2 'J' = 14 -- 1 + length cards
cardId2 card = cardId card

cardCounts2 :: String -> [Int]
cardCounts2 h = let
      m = countCards h
      j = Map.findWithDefault 0 'J' m
      -- add count of 'J's to head of list
      addj [] = [j]
      addj (x : xs) = x + j : xs
  in m & Map.delete 'J' & Map.elems & sortOn Down & addj

handType2 :: String -> Type
handType2 = countsType . cardCounts2

toHand2 :: String -> Hand
toHand2 s = Hand (handType2 s) s

handOrd2 :: Hand -> Down (Type, [Int])
handOrd2 h = Down (typ h, map cardId2 $ str h)

-- [(hand str, bid)] -> [(rank, hand, bid)]
rankBids2 :: [(String, Integer)] -> [(Integer, (Hand, Integer))]
rankBids2 bids = bids & map (first toHand2) & sortOn (handOrd2 . fst) & zip [1..]

solve2 :: [(String, Integer)] -> Integer
solve2 = sum . map (uncurry (*) . second snd) . rankBids2

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
