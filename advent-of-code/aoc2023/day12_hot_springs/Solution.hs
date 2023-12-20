{- --- Day 12: Hot Springs --- https://adventofcode.com/2023/day/12 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Function ((&))
import Data.Ord
import Data.Bifunctor
import System.IO
import Text.Parsec hiding (space, spaces)
import Control.Applicative

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- data

data Row = Row { str :: String, groups :: [Int] }
  deriving (Show, Eq)

-- parsing

tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

space :: Parsec String u Char
space = char ' '

intP :: Parsec String u Int
intP = read <$> many1 digit

rowP :: Parsec String u Row
rowP = Row <$> (many1 (oneOf ".#?") <* space) <*> sepBy intP (char ',')

parseIn :: String -> [Row]
parseIn = tryParse (endBy rowP newline)

-- part 1

tryGetGroup :: String -> Int -> Maybe (String, String)
tryGetGroup s 0 = Just ("", s)
tryGetGroup "" _ = Nothing
tryGetGroup ('.':_) _ = Nothing
tryGetGroup (c:s) n = first ('#':) <$> tryGetGroup s (n-1)

-- arrangements
newtype Prs s v = Prs { runPrs :: s -> String -> [((s, String), v)] }

instance Functor (Prs s) where
  fmap :: (a -> b) -> Prs s a -> Prs s b
  fmap f = Prs . (fmap . fmap . fmap . fmap) f . runPrs

instance Applicative (Prs s) where
  pure :: a -> Prs s a
  pure x = Prs $ \st chs -> [((st, chs), x)]
  
  (<*>) :: Prs s (a -> b) -> Prs s a -> Prs s b
  (Prs pf) <*> (Prs px) = Prs $ \st chs -> let
        fs = pf st chs
        ap ((st', chs'), f) = fmap f <$> px st' chs'
    in concatMap ap fs

charPrs :: Char -> Prs s Char
charPrs ch = Prs p where
  p _ "" = []
  p st (ch:chs) = [((st, chs), ch) | ch == ch]

stringPrs :: String -> Prs s String
stringPrs "" = pure ""
stringPrs (ch:chs) = (:) <$> charPrs ch <*> stringPrs chs

orPrs :: Prs s v -> Prs s v -> Prs s v
orPrs (Prs p1) (Prs p2) = Prs p where
  p st chs = let r1 = p1 st chs
                 r2 = p2 st chs
             in if null r1 then r2 else r1

manyPrs :: Prs s v -> Prs s [v]
manyPrs p = ((:) <$> p <*> manyPrs p) `orPrs` pure []

many1Prs :: Prs s v -> Prs s [v]
many1Prs p = (:) <$> p <*> (manyPrs p `orPrs` pure [])

manyWorkingPrs :: Prs s String
manyWorkingPrs = manyPrs $ charPrs '.'



arrs :: String -> Row -> [String]
arrs p (Row "" []) = [p]
arrs p (Row ('.':s) gs) = arrs (p ++ ".") (Row s gs)
arrs _ (Row _ []) = []
arrs p (Row s@('#':_) (n:gs)) = case tryGetGroup s n of
  Just (p', s') -> arrs (p ++ p') (Row s' gs)
  Nothing -> []
arrs p (Row ('?':s) (n:gs)) = arrs (p ++ "#") (Row s (n-1:gs))
  ++ arrs (p ++ ".") (Row s (n:gs))

solve1 :: String -> Integer
solve1 _ = 0

solution :: (String -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2

solve2 :: String -> Integer
solve2 _ = 0

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
