{- --- Day 1: Trebuchet?! --- https://adventofcode.com/2023/day/1 -}
import Data.Function ((&))
import Data.Char
import Data.List
import Data.Either
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

test1 :: Bool
test1 = testParseInput && testStrToDigits && testSumLines

processInput :: IO ()
processInput = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sumLines <$> parse parseInput fname input)
  hClose fh

-- processInput == Right 54388

spelledDigits :: [String]
spelledDigits = ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

parseSpelledDigit :: Int -> String -> Parsec String u [Int]
parseSpelledDigit n s = do
  _ <- try (string s)
  is <- getInput
  setInput $ last s : is
  return [n]

testParseSpelledDigit :: Bool
testParseSpelledDigit = parse (parseSpelledDigit 2 "two") "" "twone" == Right [2]
  && parse ((,) <$> parseSpelledDigit 2 "two" <*> parseSpelledDigit 1 "one") "" "twone"
     == Right ([2], [1])

getDigits :: Parsec [Char] u [Int]
getDigits = (singleton . digitToInt <$> digit)
  <|> choice (zipWith parseSpelledDigit [1..] spelledDigits)
  <|> [] <$ letter

testGetDigits :: Bool
testGetDigits = isLeft (parse getDigits "" "")
  && parse getDigits "" "1a2" == Right [1]
  && parse (concat <$> many1 getDigits) "" "1a2" == Right [1, 2]
  && parse (concat <$> many1 getDigits) "" "1aone2" == Right [1, 1, 2]
  && parse (concat <$> many1 getDigits) "" "ttwothree" == Right [2, 3]
  && parse (concat <$> many1 getDigits) "" "ttwone" == Right [2, 1]

parseInput2 :: Parsec [Char] u [[Int]]
parseInput2 = (concat <$> many getDigits) `sepBy` newline

testInput2 :: String
testInput2 = "two1nine\neightwothree\nabcone2threexyz\nxtwone3four\n"
  ++ "4nineeightseven2\nzoneight234\n7pqrstsixteen"

testParseInput2 :: Bool
testParseInput2 = parse parseInput2 "" testInput2
    == Right [[2, 1, 9], [8, 2, 3], [1, 2, 3], [2, 1, 3, 4], [4, 9, 8, 7, 2],
              [1, 8, 2, 3, 4], [7, 6]]
  && parse parseInput2 "" "1\n" == Right [[1], []]

digitsTails :: [Int] -> (Int, Int)
digitsTails [] = (0, 0)
digitsTails ds = (head ds, last ds)

testDigitsTails :: Bool
testDigitsTails = map (digitsToVal . digitsTails) dss == [29, 83, 13, 24, 42, 14, 76]
  where (Right dss) = parse parseInput2 "" testInput2

sumDss :: [[Int]] -> Integer
sumDss = sum . map (digitsToVal . digitsTails)

testSumDss :: Bool
testSumDss = (sumDss <$> parse parseInput2 "" testInput2) == Right 281

test2 :: Bool
test2 = testParseSpelledDigit && testGetDigits && testParseInput2
  && testDigitsTails && testSumDss

processInput2 :: IO ()
processInput2 = do
  let fname = "input.txt"
  fh <- openFile fname ReadMode
  input <- hGetContents fh
  print (sumDss <$> parse parseInput2 fname input)
  hClose fh

-- processInput2 == Right 53515

test :: Bool
test = test1 && test2
