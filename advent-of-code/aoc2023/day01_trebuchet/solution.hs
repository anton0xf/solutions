{- --- Day 1: Trebuchet?! --- https://adventofcode.com/2023/day/1 -}
import Text.Parsec
import Text.Parsec.Char

testInput :: String
testInput = "1abc2\npqr3stu8vwx\na1b2c3d4e5f\ntreb7uchet"

digitSkipLetters :: Parsec [Char] u Char
digitSkipLetters = do
  _ <- skipMany letter
  d <- digit
  _ <- skipMany letter
  return d

parseInput :: Parsec [Char] u [[Char]]
parseInput = many1 digitSkipLetters `sepBy` newline

testParseInput :: Bool
testParseInput = parse parseInput "" testInput == Right ["12", "38", "12345", "7"]
