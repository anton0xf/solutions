{- --- Day 2: Cube Conundrum --- https://adventofcode.com/2023/day/2 -}
import Data.Function ((&))
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Token
import System.IO

testInput :: String
testInput = "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green\n"
  ++ "Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue\n"
  ++ "Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red\n"
  ++ "Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red\n"
  ++ "Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green\n"

data Color = R | G | B
  deriving (Show, Eq)

data Result = Result { color :: Color, num :: Integer }
  deriving (Show, Eq)

data Game = Game { gameId :: Integer, results :: [[Result]] }
  deriving (Show, Eq)

data Bag = Bag { red :: Integer, green :: Integer, blue :: Integer }
  deriving (Show, Eq)

getFromBag :: Color -> Bag -> Integer
getFromBag R = red
getFromBag G = green
getFromBag B = blue

parseColor :: Parsec String u Color
parseColor = R <$ string "red"
  <|> G <$ string "green"
  <|> B <$ string "blue"

parseNat :: Parsec String u Integer
parseNat = read <$> many1 digit

parseResult :: Parsec String u Result
parseResult = (\n c -> Result { color = c, num = n }) <$> parseNat <* spaces <*> parseColor

parseResultTest :: Bool
parseResultTest = check "1 red" (Result R 1)
                  && check "2 green" (Result G 2)
                  && check "66 blue" (Result B 66)
  where check s r = parse parseResult "" s == Right r

parseGame :: Parsec String u Game
parseGame = Game <$> (string "Game" *> spaces *> parseNat <* char ':' <* spaces)
  <*> sepBy (sepBy parseResult (char ',' <* spaces)) (char ';' <* spaces)

parseGameTest :: Bool
parseGameTest = parse parseGame "" "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green"
  == Right Game {gameId = 1, results = [[Result B 3, Result R 4],
                                        [Result R 1, Result G 2, Result B 6],
                                        [Result G 2]]}

{- The Elf would first like to know which games would have been possible
if the bag contained only 12 red cubes, 13 green cubes, and 14 blue cubes? -}
bag1 :: Bag
bag1 = Bag { red = 12, green = 13, blue = 14 }

isResultPossible :: Bag -> Result -> Bool
isResultPossible b r = getFromBag (color r) b >= num r

isGamePossible :: Bag -> Game -> Bool
isGamePossible b g = all (all $ isResultPossible b) (results g)

parseInput :: Parsec String u [Game]
parseInput = endBy parseGame newline

testGames :: [Game]
testGames = parse parseInput "" testInput & either undefined id

isGamePossibleTest :: Bool
isGamePossibleTest = (filter (isGamePossible bag1) testGames & map gameId) == [1, 2, 5]

solution1 :: IO ()
solution1 = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sum . map gameId . filter (isGamePossible bag1) <$> parse parseInput fname input)
  hClose fh

-- solution1 == Right 2810

test :: Bool
test = parseResultTest && parseGameTest && isGamePossibleTest
