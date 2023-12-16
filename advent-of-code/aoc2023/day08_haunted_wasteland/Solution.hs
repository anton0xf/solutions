{- --- Day 8: Haunted Wasteland --- https://adventofcode.com/2023/day/8 -}
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

data Rule = Rule { node :: String, next :: (String, String) }
  deriving (Show, Eq)

data NetMap = NetMap { commands :: [Char], rules :: [Rule] }
  deriving (Show, Eq)

-- parsing
tryParse :: Parsec String () a -> String -> a
tryParse p = either undefined id . parse p ""

wordP :: Parsec String u String
wordP = many1 alphaNum

ruleP :: Parsec String u Rule
ruleP = Rule <$> (wordP <* string " = (")
  <*> ((,) <$> (wordP <* string ", ")
           <*> (wordP <* string ")"))

parseIn :: String -> NetMap
parseIn = tryParse $ NetMap
  <$> (wordP <* newline <* newline)
  <*> endBy ruleP newline

-- common

type NetSearch = String -> (String, String)

netSearch :: [Rule] -> NetSearch
netSearch = (fmap . fmap) fromJust
  $ flip Map.lookup . Map.fromList . map (\r -> (node r, next r))

-- part 1

command :: Char -> (String, String) -> String
command 'L' = fst
command 'R' = snd

step :: NetSearch -> String -> Char -> String
step s node c = command c $ s node

run :: NetMap -> String -> String -> [String]
run (NetMap commands rules) start finish = let
      s = netSearch rules
      cmds = cycle commands
  in takeWhile (/= finish) $ scanl (step s) start cmds

solve1 :: NetMap -> Integer
solve1 m = fromIntegral $ length $ run m "AAA" "ZZZ"

solution :: (NetMap -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseIn input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

-- part 2

isStart :: String -> Bool
isStart = (== 'A') . last

isFinish :: String -> Bool
isFinish = (== 'Z') . last

step2 :: NetSearch -> [String] -> Char -> [String]
step2 s nodes c = map (command c . s) nodes

run2 :: NetMap -> [[String]]
run2 (NetMap commands rules) = let
      s = netSearch rules
      cmds = cycle commands
      start = filter isStart $ map node rules
  in takeWhile (not . all isFinish) $ scanl' (step2 s) start cmds

solve2 :: NetMap -> Integer
-- solve2 = fromIntegral . length . run2
solve2 (NetMap commands rules) = let
      s = netSearch rules
      cmds = cycle $ map command commands
      start = filter isStart $ map node rules
      st (cmd : cmds) n nodes = if all isFinish nodes then n
        else st cmds (n + 1) (map (cmd . s) nodes)
  in st cmds 0 start

solution2 :: IO ()
solution2 = solution solve2

-- main

main :: IO ()
main = do
  putStr "Part 1: "
  solution1
  putStr "Part 2: "
  solution2
