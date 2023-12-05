{- --- Day 4: Scratchcards --- https://adventofcode.com/2023/day/4 -}
import Text.Parsec (Parsec, parse, many, many1, sepEndBy, digit, char, spaces, string)
import System.IO

testInput :: String
testInput = "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53\n"
         ++ "Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19\n"
         ++ "Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1\n"
         ++ "Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83\n"
         ++ "Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36\n"
         ++ "Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11\n"

data Card = Card { cardId :: Int, winNs :: [Int], yourNs :: [Int] }
  deriving (Eq, Show)

intP :: Parsec String u Int
intP = read <$> many1 digit

intsP :: Parsec String u [Int]
intsP = spaces *> sepEndBy intP spaces

cardP :: Parsec String u Card
cardP = Card <$> (string "Card" *> spaces *> intP <* char ':')
  <*> intsP <* char '|' <*> intsP

parseInput :: String -> [Card]
parseInput = either undefined id . parse (many cardP) ""

parseInputTest :: Bool
parseInputTest = parseInput testInput
  == [Card {cardId = 1, winNs = [41, 48, 83, 86, 17], yourNs = [83, 86, 6, 31, 17, 9, 48, 53]},
      Card {cardId = 2, winNs = [13, 32, 20, 16, 61], yourNs = [61, 30, 68, 82, 17, 32, 24, 19]},
      Card {cardId = 3, winNs = [1, 21, 53, 59, 44], yourNs = [69, 82, 63, 72, 16, 21, 14, 1]},
      Card {cardId = 4, winNs = [41, 92, 73, 84, 69], yourNs = [59, 84, 76, 51, 58, 5, 54, 83]},
      Card {cardId = 5, winNs = [87, 83, 26, 28, 32], yourNs = [88, 30, 70, 12, 93, 22, 82, 36]},
      Card {cardId = 6, winNs = [31, 18, 13, 56, 72], yourNs = [74, 77, 10, 23, 35, 67, 36, 11]}]


getWinningNs :: Card -> [Int]
getWinningNs card = filter (`elem` winNs card) (yourNs card)

getWinningNsTest :: Bool
getWinningNsTest = getWinningNs (Card {cardId = 1,
                                       winNs = [41, 48, 83, 86, 17],
                                       yourNs = [83, 86, 6, 31, 17, 9, 48, 53]})
                   == [83, 86, 17, 48]

winningPoints :: [Int] -> Integer
winningPoints xs = if null xs then 0
  else 2 ^ (length xs - 1)

winningPointsTest :: Bool
winningPointsTest = winningPoints [83, 86, 17, 48] == 8
  && winningPoints [32, 61] == 2
  && winningPoints [] == 0

solve1 :: [Card] -> Integer
solve1 = sum . map (winningPoints . getWinningNs)

solve1Test :: Bool
solve1Test = solve1 (parseInput testInput) == 13

test1 :: Bool
test1 = parseInputTest && getWinningNsTest && winningPointsTest && solve1Test

solution1 :: IO ()
solution1 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print (solve1 $ parseInput input)
  hClose fh

test :: Bool
test = test1
