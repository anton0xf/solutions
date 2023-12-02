{- https://stepik.org/lesson/30425/step/2?unit=11042
1.4.2. Аппликативный парсер своими руками -}

import Data.Char
import Data.Bifunctor (first)

newtype Parser a = Parser { apply :: String -> [(a, String)] }

parse :: Parser a -> String -> a
parse p = fst. head . apply p

anyChar :: Parser Char
anyChar = Parser p where
  p "" = []
  p (c : cs) = [(c, cs)]

testAnyChar :: Bool
testAnyChar = null (apply anyChar "")
  && apply anyChar "a" == [('a', "")]
  && apply anyChar "ab" == [('a', "b")]

oneOf :: [Char] -> Parser Char
oneOf cs = Parser p where
  p "" = []
  p (c : s) = [(c, s) | c `elem` cs]

testOneOf :: Bool
testOneOf = null (apply p "")
    && null (apply p "cd")
    && apply p "abc" == [('a', "bc")]
  where p = oneOf "ab"

instance Functor Parser where
  fmap :: (a -> b) -> Parser a -> Parser b
  fmap f p = Parser $ fmap (first f) . apply p

testFmap1 :: Bool
testFmap1 = null (apply p "")
           && apply p "ab" == [("ac", "b")]
  where p = fmap (: "c") anyChar

testFmap2 :: Bool
testFmap2 = null (apply p "")
    && apply p "1bc" == [(1, "bc")]
  where p = fmap digitToInt anyChar

test :: Bool
test = testAnyChar && testOneOf && testFmap1 && testFmap2
