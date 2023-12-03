{- --- Day 1: Trebuchet?! --- https://adventofcode.com/2023/day/1 -}
import Data.Function ((&))
import Data.Char
import Text.Parsec
import Text.Parsec.Char
import System.IO

testInput :: String
testInput = "1abc2\npqr3stu8vwx\na1b2c3d4e5f\ntreb7uchet"

digitSkipLetters :: Parsec [Char] u String
digitSkipLetters = ((: "") <$> digit) <|> "" <$ letter

parseInput :: Parsec [Char] u [String]
parseInput = (concat <$> many digitSkipLetters) `sepBy` newline

testParseInput :: Bool
testParseInput = parse parseInput "" testInput == Right ["12", "38", "12345", "7"]
  && parse parseInput "" "1\n" == Right ["1", ""]

strToDigits :: String -> (Int, Int)
strToDigits "" = (0, 0)
strToDigits s = (head s & digitToInt, last s & digitToInt)

testStrToDigits :: Bool
testStrToDigits = strToDigits "12" == (1, 2)
  && strToDigits "38" == (3, 8)
  && strToDigits "12345" == (1, 5)
  && strToDigits "7" == (7, 7)
  && strToDigits "" == (0, 0)

digitsToVal :: (Int, Int) -> Integer
digitsToVal (d1, d2) = toInteger d1 * 10 + toInteger d2

sumLines :: [String] -> Integer
sumLines = sum . map (digitsToVal . strToDigits)

testSumLines :: Bool
testSumLines = (sumLines <$> parse parseInput "" testInput) == Right 142

test :: Bool
test = testParseInput && testStrToDigits && testSumLines

processInput :: IO ()
processInput = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sumLines <$> parse parseInput fname input)
  hClose fh

-- processInput == Right 54388


