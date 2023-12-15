{- --- Day 5: If You Give A Seed A Fertilizer --- https://adventofcode.com/2023/day/5 -}
{- install dependency:
$ cabal install --lib parsec -}
module Solution where

import Data.Maybe
import Data.Function ((&))
import Control.Monad
import System.IO
import Text.Parsec hiding (space, spaces)

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

convRuleP :: Parsec String u ConvRule
convRuleP = convRule <$> intsP

convMapP :: Parsec String u ConvMap
convMapP = ConvMap <$> (nameP <* string "-to-")
  <*> (nameP <* spaces <* string "map:" <* spaces <* newline)
  <*> sepEndBy convRuleP newline

almanacP :: Parsec String u Almanac
almanacP = Almanac <$> (string "seeds:" *> spaces *> intsP <* newline)
  <*> (newline *> sepEndBy convMapP newline)

parseInput :: String -> Almanac
parseInput = either undefined id . parse almanacP ""

-- solution

data Range = Range { start :: Integer, len :: Integer }
  deriving (Eq, Show)

rangeEnd :: Range -> Integer
rangeEnd (Range s l) = s + l - 1

rangeEnds :: Range -> (Integer, Integer)
rangeEnds r = (start r, rangeEnd r)

rangePoints :: Range -> [Integer]
rangePoints r = let (s, e) = rangeEnds r
                in [s..e]

srcRange :: ConvRule -> Range
srcRange rule = Range (srcStart rule) (rangeLen rule)

inRange :: Integer -> Range -> Bool
inRange x (Range s l) = s <= x && x < s + l

rangeByEnds :: Integer -> Integer -> Range
rangeByEnds s e = Range s (e - s + 1)

applyConvRule :: ConvRule -> Integer -> Maybe Integer
applyConvRule rule@(ConvRule dst src len) x = if inRange x (srcRange rule)
  then Just $ dst - src + x
  else Nothing

applyConvMap :: ConvMap -> Integer -> Integer
applyConvMap m x = msum (map (($ x) . applyConvRule) (rules m)) & fromMaybe x

applyConvMaps :: [ConvMap] -> Integer -> Integer
applyConvMaps ms x = foldl (flip applyConvMap) x ms

solve1 :: Almanac -> Integer
solve1 (Almanac ss ms) = minimum $ map (applyConvMaps ms) ss

solution :: (Almanac -> Integer) -> IO ()
solution solve = do
  fh <- openFile "input.txt" ReadMode
  input <- hGetContents fh
  print $ solve $ parseInput input
  hClose fh

solution1 :: IO ()
solution1 = solution solve1

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

justApplyConvRule' :: ConvRule -> Range -> Range
justApplyConvRule' rule (Range start len) = Range (fromJust $ applyConvRule rule start) len

-- apply ConvRule to intersection of the source rule interval with range
-- return result and rest of input intervals without the source rule interval
applyConvRule' :: ConvRule -> Range -> (Maybe Range, [Range])
applyConvRule' rule range =
  let (inter, rest) = intersectL range (srcRange rule)
      res = justApplyConvRule' rule <$> inter
  in (res, rest)

-- rule -> ranges -> (ranges from dst, ranges from src)
applyConvRule'' :: ConvRule -> [Range] -> ([Range], [Range])
applyConvRule'' rule = foldl merge ([], []) . map (applyConvRule' rule)
  where merge (accDst, accSrc) (maybeDst, src) = (accDst ++ maybeToList maybeDst, accSrc ++ src)

applyConvMap' :: ConvMap -> [Range] -> [Range]
applyConvMap' m rs = uncurry (++) $ foldl merge ([], rs) (rules m)
  where
    merge :: ([Range], [Range]) -> ConvRule -> ([Range], [Range])
    merge (dst, src) rule = let (dst', src') = applyConvRule'' rule src
                            in (dst ++ dst', src')

applyConvMaps' :: [ConvMap] -> [Range] -> [Range]
applyConvMaps' ms rs = foldl (flip applyConvMap') rs ms

solve2 :: Almanac -> Integer
solve2 (Almanac seeds maps) = seeds & seedsToRanges
  & applyConvMaps' maps & map start & minimum

solution2 :: IO ()
solution2 = solution solve2
