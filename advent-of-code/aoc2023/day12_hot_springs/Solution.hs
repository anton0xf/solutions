{- --- Day 12: Hot Springs --- https://adventofcode.com/2023/day/12 -}
module Solution where

import Data.Maybe
import Data.List hiding ((\\))
import Data.Ord
import Data.Function
import Data.Functor
import Data.Bifunctor
import System.IO
import Text.Parsec hiding (space, spaces, State)
import Control.Applicative
import Control.Monad.List
import Control.Monad.State

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

data CRow = CRow [NChars] [Int] deriving (Show, Eq, Ord)

compressRow :: Row -> CRow
compressRow (Row chs gs) = CRow (compressChs chs) gs

uncompressRow :: CRow -> Row
uncompressRow (CRow nchs gs) = Row (uncompressNChs nchs) gs

-- CRow arrangements

type ArrSt = State (Map (Bool, CRow) Integer)

-- sep -> row -> compressed strings
arrsc :: (Bool -> CRow -> ArrSt Integer) -> Bool -> CRow -> ArrSt Integer
-- empty tail
arrsc _ _ (CRow [] []) = return 1
-- empty string
arrsc _ _ (CRow [] _) = return 0
-- if there are no groups left then the tail can contain only dots (working springs)
arrsc arrs _ (CRow (('.', n) : chs) gs) = arrs True (CRow chs gs)
arrsc _ _ (CRow (('#', _) : _) []) = return 0
arrsc arrs _ (CRow (('?', n) : chs) []) = arrs True (CRow chs [])
-- '#' can't be sep
arrsc _ False (CRow (('#', _) : _) _) = return 0
-- '#' starts group
arrsc arrs True (CRow chs@(('#', _) : _) (g : gs)) = case readNW g chs of
      Nothing -> return 0
      Just chs' -> arrs False (CRow chs' gs)
-- read some starting '?' as '.' then starts group
-- or treat all '?' as '.'
arrsc arrs sep (CRow (ch@('?', n) : chs) (g : gs)) = do
      rg <- readG
      rw <- skipW
      return $ rw + rg
  where
        readG :: ArrSt Integer
        readG = do
            -- [(woring prefix size, rest arragments' count)]
            rstss <- traverse (uncurry readRest) wnw
            return $ sum . map snd $ rstss

        -- working prefix size -> rest after reading following not-working group
        wnw :: [(Int, [NChars])]
        wnw = do
          -- length of prefix with working springs
          wn <- [(if sep then 0 else 1) .. (n - 1)]
          -- chars of following not-working group
          nwg <- maybeToList $ readNW g (('?', n - wn) : chs)
          return (wn, nwg)

        readRest :: Int -> [NChars] -> ArrSt (Int, Integer)
        readRest nw chs = do
          rsts <- arrs False (CRow chs gs)
          return (nw, rsts)

        skipW :: ArrSt Integer
        skipW = arrs True (CRow chs (g : gs))


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

arrsc' :: Bool -> CRow -> Integer
arrsc' sep = flip evalState Map.empty . fix arrsc sep

arrscMemo :: (Bool -> CRow -> ArrSt Integer) -> Bool -> CRow -> ArrSt Integer
arrscMemo arrs sep row = do
  m <- get
  case Map.lookup (sep, row) m of
    Nothing -> do
      ress <- arrs sep row
      modify (Map.insert (sep, row) ress)
      return ress
    Just ress -> return ress


arrsc'' :: Bool -> CRow -> Integer
arrsc'' sep row = evalState (fix (arrscMemo . arrsc) sep row) Map.empty

-- solution 1

solve1 :: String -> Integer
solve1 = sum . map (arrsc'' True . compressRow) . parseIn

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

arrs2 :: Row -> Integer
arrs2 = arrsc'' True . compressRow . unfoldRow 5

solve2 :: String -> Integer
solve2 = sum . map arrs2 . parseIn

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
