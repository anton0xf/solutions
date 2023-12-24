{- --- Day 12: Hot Springs --- https://adventofcode.com/2023/day/12 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Ord
import Data.Function ((&))
import Data.Functor
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
type NChars = (Char, Int)

compressChs :: String -> [NChars]
compressChs "" = []
compressChs chs@(ch:_) = let (nch, chs') = span (== ch) chs
                         in (ch, length nch) : compressChs chs'

uncompressNChs :: [NChars] -> String
uncompressNChs [] = ""
uncompressNChs ((c, n) : chs) = replicate n c ++ uncompressNChs chs

data CRow = CRow [NChars] [Int] deriving (Show, Eq)

compressRow :: Row -> CRow
compressRow (Row chs gs) = CRow (compressChs chs) gs

uncompressRow :: CRow -> Row
uncompressRow (CRow nchs gs) = Row (uncompressNChs nchs) gs

-- CRow arrangements
-- sep -> row -> compressed strings
arrsc :: Bool -> CRow -> [[NChars]]
-- empty tail
arrsc _ (CRow [] []) = [[]]
-- empty string
arrsc _ (CRow [] _) = []
-- if there are no groups left then the tail can contain only dots (working springs)
arrsc _ (CRow (('.', n) : chs) gs) = (:) <$> [('.', n)] <*> arrsc True (CRow chs gs)
arrsc _ (CRow (('#', _) : _) []) = []
arrsc _ (CRow (('?', n) : chs) []) = (:) <$> [('.', n)] <*> arrsc True (CRow chs [])
-- '#' can't be sep
arrsc False (CRow (('#', _) : _) _) = []
-- '#' starts group
arrsc True (CRow chs@(('#', _) : _) (g : gs)) = case readNW g chs of
      Nothing -> []
      Just chs' -> (++) <$> [[('#', g)]] <*> arrsc False (CRow chs' gs)
-- read some starting '?' as '.' then starts group
-- or treat all '?' as '.'
arrsc sep (CRow (ch@('?', n) : chs) (g : gs)) = readG ++ skipW
   where readG = do
           n' <- [(if sep then 0 else 1) .. (n - 1)]
           chs' <- maybeToList $ readNW g (('?', n - n') : chs)
           rest <- arrsc False (CRow chs' gs)
           return $ [('.', n') | n' /= 0] ++ ('#', g) : rest
         skipW = (:) <$> [('.', n)] <*> arrsc True (CRow chs (g : gs))

-- try to read g not-working chars ('#' or '?') and return rest of chs
readNW :: Int -> [NChars] -> Maybe [NChars]
readNW 0 chs = Just chs
readNW _ [] = Nothing
readNW _ (('.', _) : _) = Nothing
readNW g (('#', n) : chs)
  | g <  n = Nothing
  | g == n = Just chs
  | g >  n = readNW (g - n) chs
readNW g (('?', n) : chs)
  | g <  n = Just $ ('?', n - g) : chs
  | g == n = Just chs
  | g >  n = readNW (g - n) chs

-- try to read only working chars ('.' or '?') to the end of string
readRestW :: [NChars] -> Maybe Int
readRestW [] = Just 0
readRestW (('#',_) : _) = Nothing
readRestW ((_, n) : chs) = do
  n' <- readRestW chs
  return (n + n')

-- solution 1

solve1 :: String -> Integer
solve1 = sum . map (fromIntegral . length . arrsc True . compressRow) . parseIn

solution :: (String -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2

unfoldRow :: Int -> Row -> Row
unfoldRow n (Row chs gs) = Row (intercalate "?" $ replicate n chs) (concat $ replicate n gs)

arrs2 :: Row -> [[NChars]]
arrs2 = arrsc True . compressRow . unfoldRow 5

solve2 :: String -> Integer
solve2 = sum . map (fromIntegral . length . arrs2) . parseIn

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
