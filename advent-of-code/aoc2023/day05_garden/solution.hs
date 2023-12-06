{- --- Day 5: If You Give A Seed A Fertilizer --- https://adventofcode.com/2023/day/5 -}
import Data.Maybe
import Data.Either
import Data.List
import Data.Function ((&))
import Control.Monad
import System.IO
import Text.Parsec hiding (space, spaces)

testInput :: String
testInput = "seeds: 79 14 55 13\n"
         ++ "\n"
         ++ "seed-to-soil map:\n"
         ++ "50 98 2\n"
         ++ "52 50 48\n"
         ++ "\n"
         ++ "soil-to-fertilizer map:\n"
         ++ "0 15 37\n"
         ++ "37 52 2\n"
         ++ "39 0 15\n"
         ++ "\n"
         ++ "fertilizer-to-water map:\n"
         ++ "49 53 8\n"
         ++ "0 11 42\n"
         ++ "42 0 7\n"
         ++ "57 7 4\n"
         ++ "\n"
         ++ "water-to-light map:\n"
         ++ "88 18 7\n"
         ++ "18 25 70\n"
         ++ "\n"
         ++ "light-to-temperature map:\n"
         ++ "45 77 23\n"
         ++ "81 45 19\n"
         ++ "68 64 13\n"
         ++ "\n"
         ++ "temperature-to-humidity map:\n"
         ++ "0 69 1\n"
         ++ "1 0 69\n"
         ++ "\n"
         ++ "humidity-to-location map:\n"
         ++ "60 56 37\n"
         ++ "56 93 4\n"

data ConvRule = ConvRule { dstStart :: Integer, srcStart :: Integer, rangeLen :: Integer }
  deriving (Eq, Show)

convRule :: [Integer] -> ConvRule
convRule [ds, ss, len] = ConvRule ds ss len
convRule ns = error ("convRule: unexpected input: " ++ show ns)

data ConvMap = ConvMap { src :: String, dst :: String, rules :: [ConvRule] }
  deriving (Eq, Show)

data Almanac = Almanac { seeds :: [Integer], maps :: [ConvMap] }
  deriving (Eq, Show)

space :: Parsec String u Char
space = char ' '

spaces :: Parsec String u String
spaces = many space

intP :: Parsec String u Integer
intP = read <$> many1 digit

intsP :: Parsec String u [Integer]
intsP = spaces *> sepEndBy1 intP spaces

nameP :: Parsec String u String
nameP = many1 letter

testSeedMap :: String
testSeedMap = "seed-to-soil map:\n"
          ++ "50 98 2\n"
          ++ "52 50 48\n"

convRuleP :: Parsec String u ConvRule
convRuleP = convRule <$> intsP

convRulePTest :: Bool
convRulePTest = parse convRuleP "" "50 98 2"
  == Right (ConvRule {dstStart = 50, srcStart = 98, rangeLen = 2})

convMapP :: Parsec String u ConvMap
convMapP = ConvMap <$> (nameP <* string "-to-")
  <*> (nameP <* spaces <* string "map:" <* spaces <* newline)
  <*> sepEndBy convRuleP newline

convMapPTest :: Bool
convMapPTest = parse convMapP "" testSeedMap
  == Right (ConvMap {src = "seed", dst = "soil",
                     rules = [ConvRule {dstStart = 50, srcStart = 98, rangeLen = 2},
                              ConvRule {dstStart = 52, srcStart = 50, rangeLen = 48}]})

almanacP :: Parsec String u Almanac
almanacP = Almanac <$> (string "seeds:" *> spaces *> intsP <* newline)
  <*> (newline *> sepEndBy convMapP newline)

parseInput :: String -> Almanac
parseInput = either undefined id . parse almanacP ""

parseInputTest :: Bool
parseInputTest = let almanac = parseInput testInput
  in (almanac & seeds) == [79, 14, 55, 13]
     && (almanac & maps & length) == 7
     && (almanac & maps & head & Right) == parse convMapP "" testSeedMap

isInRange :: Integer -> Integer -> Integer -> Bool
isInRange x start len = start <= x && x < start + len

isInRangeTest :: Bool
isInRangeTest = not (isInRange 0 3 2) && not (isInRange 2 3 2)
  && isInRange 3 3 2 && isInRange 4 3 2
  && not (isInRange 5 3 2) && not (isInRange 10 3 2)

applyConvRule :: ConvRule -> Integer -> Maybe Integer
applyConvRule (ConvRule dst src len) x = if isInRange x src len
  then Just $ dst - src + x
  else Nothing

applyConvRuleTest :: Bool
applyConvRuleTest = isNothing (applyConvRule r 1)
                 && applyConvRule r 2 == Just 10
                 && applyConvRule r 4 == Just 12
                 && isNothing (applyConvRule r 5)
  where r = ConvRule 10 2 3

applyConvMap :: ConvMap -> Integer -> Integer
applyConvMap m x = msum (map (($ x) . applyConvRule) (rules m)) & fromMaybe x

applyConvMapTest :: Bool
applyConvMapTest = m 0 == 0
                && m 49 == 49
                && m 50 == 52
                && m 97 == 99
                && m 98 == 50
                && m 99 == 51
                && m 100 == 100
                && m 200 == 200
                && map m [79, 14, 55, 13] == [81, 14, 57, 13]
  where m = applyConvMap (parse convMapP "" testSeedMap & fromRight undefined)

applyConvMaps :: [ConvMap] -> Integer -> Integer
applyConvMaps ms x = foldl (flip applyConvMap) x ms

applyConvMapsTest :: Bool
applyConvMapsTest = map (applyConvMaps (maps a)) (seeds a) == [82, 43, 86, 35]
  where a = parseInput testInput

solve1 :: Almanac -> Integer
solve1 (Almanac ss ms) = minimum $ map (applyConvMaps ms) ss

solve1Test :: Bool
solve1Test = solve1 (parseInput testInput) == 35

test1 :: Bool
test1 = convRulePTest && convMapPTest && parseInputTest
  && isInRangeTest && applyConvRuleTest && applyConvMapTest && applyConvMapsTest
  && solve1Test

solution1 :: IO ()
solution1 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve1 $ parseInput input
  hClose fh
