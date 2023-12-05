{- --- Day 3: Gear Ratios --- https://adventofcode.com/2023/day/3 -}

import Data.Char (isDigit)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)
import Data.Bifunctor (bimap, second)
import System.IO ( IOMode(ReadMode), hClose, hGetContents, openFile )
import Text.Parsec

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

testInput :: String
testInput = "467..114..\n"
         ++ "...*......\n"
         ++ "..35..633.\n"
         ++ "......#...\n"
         ++ "617*......\n"
         ++ ".....+.58.\n"
         ++ "..592.....\n"
         ++ "......755.\n"
         ++ "...$.*....\n"
         ++ ".664.598..\n"

data Pos = Pos { row :: Int, col :: Int }
  deriving (Show, Eq, Ord)

convertSourcePos :: SourcePos -> Pos
convertSourcePos s = Pos (sourceLine s) (sourceColumn s)

dots :: Parsec String u String
dots = many (char '.')

notDigit :: Parsec String u String
notDigit = many $ satisfy (not . isDigit)

partNum :: Parsec String u (Pos, String)
partNum = do
  _ <- notDigit
  pos <- getPosition <&> convertSourcePos
  num <- many1 digit
  _ <- notDigit
  return (pos, num)

-- get all partNums with positions:
-- > parseTest (many partNum) testInput

symbol :: Parsec String u (Pos, Char)
symbol = do
  let notSym = many $ satisfy (\c -> isDigit c || c == '.' || c == '\n')
  _ <- notSym
  pos <- getPosition <&> convertSourcePos
  num <- anyChar
  _ <- notSym
  return (pos, num)

-- get all symbols with positions:
-- > parseTest (many symbol) testInput

neighbours :: (Pos, String) -> [Pos]
neighbours (Pos pr pc, s) = [Pos pr (pc - 1), Pos pr (pc + length s)]
  ++ [Pos r c | r <- [pr - 1, pr + 1], c <- [(pc - 1) .. (pc + length s)]]

getPartNums :: String -> String -> [Integer]
getPartNums fname s = let
    (Right nums) = parse (many partNum) fname s
    (Right symbols) = parse (many symbol) fname s
    syms = Map.fromList symbols :: Map Pos Char
    hasMemberSym = any (`Map.member` syms) . neighbours :: (Pos, String) -> Bool
  in map (read . snd) $ filter hasMemberSym nums

getPartNumsTest :: Bool
getPartNumsTest = getPartNums "" testInput == [467, 35, 633, 617, 592, 755, 664, 598]
  && sum (getPartNums "" testInput) == 4361

test1 :: Bool
test1 = getPartNumsTest

solution1 :: IO ()
solution1 = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sum $ getPartNums fname input)
  hClose fh

getNeighboursMap :: [(Pos, String)] -> Map Pos [(Pos, String)]
getNeighboursMap nums = Map.fromListWith (++) (concatMap invNeighbours nums)
  where invNeighbours :: (Pos, String) -> [(Pos, [(Pos, String)])]
        invNeighbours pn = map (, [pn]) (neighbours pn)

getGear :: Map Pos [(Pos, String)] -> (Pos, Char)
  -> Maybe (Pos, ((Pos, String), (Pos, String)))
getGear neighboursMap (pos, sym) = do
  gearNums <- Map.lookup pos neighboursMap
  if sym == '*' && length gearNums == 2
    then let [n1, n2] = gearNums in return (pos, (n1, n2))
    else Nothing

getGears :: String -> String -> [(Pos, (Integer, Integer))]
getGears fname s = let
    Right nums = parse (many partNum) fname s
    Right (symbols :: [(Pos, Char)]) = parse (many symbol) fname s
    neighboursMap = getNeighboursMap nums :: Map Pos [(Pos, String)]
    getNum = read . snd
  in map (second (bimap getNum getNum)) . mapMaybe (getGear neighboursMap) $ symbols

getGearsTest :: Bool
getGearsTest = getGears "" testInput
  == [(Pos {row = 2, col = 4}, (35, 467)),
      (Pos {row = 9, col = 6}, (598, 755))]

test2 :: Bool
test2 = getGearsTest

solution2 :: IO ()
solution2 = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sum . map (uncurry (*) . snd) $ getGears fname input)
  hClose fh

test :: Bool
test = test1 && test2
