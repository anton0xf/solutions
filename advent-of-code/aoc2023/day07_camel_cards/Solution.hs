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
cardId card = Map.lookup card cardIds & fromMaybe 0

handOrd :: Hand -> Down (Type, [Int])
handOrd h = Down (typ h, map cardId $ str h)

instance Ord Hand where
  compare :: Hand -> Hand -> Ordering
  compare x y = compare (handOrd x) (handOrd y)

countCards :: String -> Map Char Int
countCards = foldl add Map.empty
  where add m card = Map.insertWith (+) card 1 m

handType :: String -> Type
handType h = case countCards h & Map.elems & sortOn Down of
  5 : _ -> Five
  4 : _ -> Four
  3 : 2 : _ -> FullHouse
  3 : _ -> Three
  2 : 2 : _ -> TwoPair
  2 : _ -> Pair
  _ -> High

toHand :: String -> Hand
toHand s = Hand (handType s) s

-- part 1

-- [(hand str, bid)] -> [(rank, hand, bid)]
rankBids :: [(String, Integer)] -> [(Integer, (Hand, Integer))]
rankBids bids = bids & map (first toHand) & sortOn fst & zip [1..]

solve1 :: [(String, Integer)] -> Integer
solve1 = sum . map (uncurry (*) . second snd) . rankBids

solution1 :: IO ()
solution1 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve1 $ parseInput input
  hClose fh

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
