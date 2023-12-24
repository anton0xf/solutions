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

tryGetGroup :: String -> Int -> Maybe (String, String)
tryGetGroup s 0 = Just ("", s)
tryGetGroup "" _ = Nothing
tryGetGroup ('.':_) _ = Nothing
tryGetGroup (c:s) n = first ('#':) <$> tryGetGroup s (n-1)

-- Prs
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

updStPrs :: (s -> s) -> Prs s ()
updStPrs f = Prs $ \st chs -> [((f st, chs), ())]

charPrs :: Char -> Prs s Char
charPrs ch = Prs p where
  p _ "" = []
  p st (h:chs) = [((st, chs), ch) | h == ch]

anyCharPrs :: Prs s Char
anyCharPrs = Prs p where
  p _ "" = []
  p st (ch:chs) = [((st, chs), ch)]

satisfyPrs :: (Char -> Bool) -> Prs s Char
satisfyPrs pred = Prs p where
  p _ "" = []
  p st (ch:chs) = [((st, chs), ch) | pred ch]

stringPrs :: String -> Prs s String
stringPrs "" = pure ""
stringPrs (ch:chs) = (:) <$> charPrs ch <*> stringPrs chs

orPrs :: Prs s v -> Prs s v -> Prs s v
orPrs (Prs p1) (Prs p2) = Prs p where
  p st chs = let r1 = p1 st chs
                 r2 = p2 st chs
             in if null r1 then r2 else r1

variantPrs :: Prs s v -> Prs s v -> Prs s v
variantPrs (Prs p1) (Prs p2) = Prs p where
  p st chs = p1 st chs ++ p2 st chs

manyPrs :: Prs s v -> Prs s [v]
manyPrs p = ((:) <$> p <*> manyPrs p) `orPrs` pure []

many1Prs :: Prs s v -> Prs s [v]
many1Prs p = (:) <$> p <*> (manyPrs p `orPrs` pure [])

countPrs :: Int -> Prs s v -> Prs s [v]
countPrs 0 _ = pure []
countPrs n p = (:) <$> p <*> countPrs (n-1) p

pairList :: a -> a -> [a]
pairList x y = [x, y]

-- separated and enclosed by 
sepEncByPrs :: Prs s v -> Prs s v -> Prs s [v]
sepEncByPrs p sep = (:) <$> sep <*> (concat <$> manyPrs (pairList <$> p <*> sep))

-- arrangements
type ArrPrs v = Prs (Bool, [Int]) v

setSep :: Bool -> ArrPrs ()
setSep b = updStPrs $ first $ const b

setGroups :: [Int] -> ArrPrs ()
setGroups gs = updStPrs $ second $ const gs

readWorking :: ArrPrs Char
readWorking = charPrs '.' <* setSep True

readNotWorking :: ArrPrs Char
readNotWorking = satisfyPrs (/= '.') $> '#' <* setSep False

readGroup :: ArrPrs String
readGroup = Prs p where
  p (True, []) _ = []
  p st@(True, g:gs) chs@(ch:_) = runPrs (countPrs g readNotWorking <* setGroups gs) st chs
  p _ _ = []

readMaybeWorking :: ArrPrs String
readMaybeWorking = charPrs '?' $> "." <* setSep True

readArrs :: Prs (Bool, [Int]) String
-- readArrs = (++) <$> manyPrs readWorking <*> variantPrs readMaybeWorking readGroup
readArrs = concat <$> sepEncByPrs (variantPrs readMaybeWorking readGroup) (manyPrs readWorking)

arrs :: Row -> [String]
arrs (Row chs gs) = map snd . filter parsed . runPrs readArrs (True, gs) $ chs
  where parsed (((_, gs), chs), str) = null gs && null chs

-- compress row
type NChars = (Char, Int)

compressChs :: String -> [NChars]
compressChs "" = []
compressChs chs@(ch:_) = let (nch, chs') = span (== ch) chs
                         in (ch, length nch) : compressChs chs'

data CRow = CRow [NChars] [Int] deriving (Show, Eq)

compressRow :: Row -> CRow
compressRow (Row chs gs) = CRow (compressChs chs) gs

-- CRow arrangements
-- sep -> row -> compressed strings
arrsc :: Bool -> CRow -> [[NChars]]
arrsc _ (CRow [] []) = [[]]
arrsc _ (CRow (ch@('.', _):chs) gs) = (++) <$> [[ch]] <*> arrsc True (CRow chs gs)
arrsc False (CRow (('#', _) : _) _) = []
arrsc True (CRow chs@(('#', _) : _) (g : gs)) = case readNW g chs of
      Nothing -> []
      Just chs' -> (++) <$> [[('#', g)]] <*> arrsc False (CRow chs' gs)
arrsc sep (CRow (ch@('?', n) : chs) (g : gs)) = do
  n' <- [(if sep then 0 else 1) .. n]
  chs' <- maybeToList $ readNW g (('?', n - n') : chs)
  rest <- arrsc False (CRow chs' gs)
  return $ [('.', n') | n' /= 0] ++ ('#', g) : rest

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

-- solution 1

solve1' :: String -> Integer
solve1' = sum . map (fromIntegral . length . arrs) . parseIn

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

arrs2' :: Row -> [String]
arrs2' = arrs . unfoldRow 5

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
