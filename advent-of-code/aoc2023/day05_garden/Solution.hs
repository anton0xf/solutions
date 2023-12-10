{- --- Day 5: If You Give A Seed A Fertilizer --- https://adventofcode.com/2023/day/5 -}
module Solution where

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

-- input data structure

data ConvRule = ConvRule { dstStart :: Integer, srcStart :: Integer, rangeLen :: Integer }
  deriving (Eq, Show)

convRule :: [Integer] -> ConvRule
convRule [ds, ss, len] = ConvRule ds ss len
convRule ns = error ("convRule: unexpected input: " ++ show ns)

data ConvMap = ConvMap { src :: String, dst :: String, rules :: [ConvRule] }
  deriving (Eq, Show)

data Almanac = Almanac { seeds :: [Integer], maps :: [ConvMap] }
  deriving (Eq, Show)

-- parsing

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

-- solution

data Range = Range { start :: Integer, len :: Integer }
  deriving (Eq, Show)

rangeEnd :: Range -> Integer
rangeEnd (Range s l) = s + l - 1

rangeEnds :: Range -> (Integer, Integer)
rangeEnds r = (start r, rangeEnd r)

srcRange :: ConvRule -> Range
srcRange rule = Range (srcStart rule) (rangeLen rule)

inRange :: Integer -> Range -> Bool
inRange x (Range s l) = s <= x && x < s + l

inRangeTest :: Bool
inRangeTest = not (inRange 0 (Range 3 2)) && not (inRange 2 (Range 3 2))
  && inRange 3 (Range 3 2) && inRange 4 (Range 3 2)
  && not (inRange 5 (Range 3 2)) && not (inRange 10 (Range 3 2))

rangeByEnds :: Integer -> Integer -> Range
rangeByEnds s e = Range s (e - s + 1)

applyConvRule :: ConvRule -> Integer -> Maybe Integer
applyConvRule rule@(ConvRule dst src len) x = if inRange x (srcRange rule)
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
  && inRangeTest && applyConvRuleTest && applyConvMapTest && applyConvMapsTest
  && solve1Test

solution1 :: IO ()
solution1 = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve1 $ parseInput input
  hClose fh

-- part 2

seedsToRanges :: [Integer] -> [Range]
seedsToRanges [] = []
seedsToRanges [_] = error "expected even-sized list"
seedsToRanges (start : len : ns) = Range start len : seedsToRanges ns

intersectL :: Range -> Range -> (Maybe Range, [Range])
intersectL r1@(Range s1 l1) r2@(Range s2 l2) =
  let r1e = rangeEnd r1
      r2e = rangeEnd r2
  in if s1 < s2 then (if inRange r1e r2
                      then (Just $ rangeByEnds s2 r1e, [rangeByEnds s1 (s2 - 1)])
                      else if r1e < s2 then (Nothing, [r1])
                      else (Just r2, [rangeByEnds s1 (s2 - 1), rangeByEnds (r2e + 1) r1e]))
  else if inRange s1 r2 then (if inRange r1e r2
                              then (Just r1, [])
                              else (Just $ rangeByEnds s1 r2e, [rangeByEnds (r2e + 1) r1e]))
  else (Nothing, [r1])

intersectLTest :: Bool
intersectLTest = intersectL r1 r == (Nothing, [r1])
                 && intersectL (Range 1 2) r == (Just $ Range 2 1, [Range 1 1])
                 && intersectL (Range 1 3) r == (Just $ Range 2 2, [Range 1 1])
                 && intersectL (Range 1 7) r == (Just r, [Range 1 1, Range 5 3])
                 && intersectL (Range 3 2) r == (Just $ Range 3 2, [])
                 && intersectL (Range 3 4) r == (Just $ Range 3 2, [Range 5 2])
                 && intersectL (Range 5 1) r == (Nothing, [Range 5 1])
  where r = Range 2 3
        r1 = Range 0 1

justApplyConvRule' :: ConvRule -> Range -> Range
justApplyConvRule' rule (Range start len) = Range (fromJust $ applyConvRule rule start) len

-- apply ConvRule to intersection of the source rule interval with range
-- return result and rest of input intervals without the source rule interval
applyConvRule' :: ConvRule -> Range -> (Maybe Range, [Range])
applyConvRule' rule range =
  let (inter, rest) = intersectL range (srcRange rule)
      res = justApplyConvRule' rule <$> inter
  in (res, rest)

applyConvRule'Test :: Bool
applyConvRule'Test = f (Range 0 2) == (Nothing, [Range 0 2])
                     && f (Range 1 2) == (Just $ Range 10 1, [Range 1 1])
                     && f (Range 2 1) == (Just $ Range 10 1, [])
                     && f (Range 4 1) == (Just $ Range 12 1, [])
                     && f (Range 5 2) == (Nothing, [Range 5 2])
                     && f1 (Range 1 200) == (Just $ Range 50 2, [Range 1 97, Range 100 101])
                     && f2 (Range 1 97) == (Just $ Range 52 48, [Range 1 49])
                     && f2 (Range 100 101) == (Nothing, [Range 100 101])
  where f = applyConvRule' $ ConvRule 10 2 3
        f1 = applyConvRule' $ ConvRule 50 98 2
        f2 = applyConvRule' $ ConvRule 52 50 48

-- rule -> ranges -> (ranges from src, ranges from dst)
applyConvRule'' :: ConvRule -> [Range] -> ([Range], [Range])
applyConvRule'' rule = foldl merge ([], []) . map (applyConvRule' rule)
  where merge (accDst, accSrc) (maybeDst, src) = (accDst ++ maybeToList maybeDst, accSrc ++ src)

applyConvRule''Test :: Bool
applyConvRule''Test = f1 [Range 1 200] == ([Range 50 2], [Range 1 97, Range 100 101])
                      && f2 [Range 1 97] == ([Range 52 48], [Range 1 49])
                      && f2 [Range 100 101] == ([], [Range 100 101])
  where f1 = applyConvRule'' $ ConvRule 50 98 2
        f2 = applyConvRule'' $ ConvRule 52 50 48

applyConvMap' :: ConvMap -> [Range] -> [Range]
applyConvMap' m rs = undefined -- foldl (flip applyConvRule'') rs (rules m)

applyConvMap'Test :: Bool
applyConvMap'Test = m [Range 1 49, Range 50 48] == [Range 1 49, Range 52 48]
                    && m [Range 1 97] == [Range 52 48, Range 1 49]
                    -- && m [Range 1 200] == [Range ]
                -- && m 98 == 50
                -- && m 99 == 51
                -- && m 100 == 100
                -- && m 200 == 200
                -- && map m [79, 14, 55, 13] == [81, 14, 57, 13]
  where m = applyConvMap' (parse convMapP "" testSeedMap & fromRight undefined)

applyConvMaps' :: [ConvMap] -> [Range] -> [Range]
applyConvMaps' ms rs = undefined -- foldl (flip applyConvMap') x ms

applyConvMaps'Test :: Bool
applyConvMaps'Test = undefined -- map (applyConvMaps' (maps a)) (seeds a) == [82, 43, 86, 35]
  where a = parseInput testInput


test2 :: Bool
test2 = intersectLTest && applyConvRule'Test && applyConvRule''Test && applyConvMap'Test

test :: Bool
test = test1 && test2
