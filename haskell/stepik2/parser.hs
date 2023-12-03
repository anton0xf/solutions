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

-- https://stepik.org/lesson/30425/step/7?unit=11042
satisfy :: (Char -> Bool) -> Parser Char
satisfy pred = Parser p where
  p "" = []
  p (c : cs) = [(c, cs) | pred c]

oneOf :: [Char] -> Parser Char
-- oneOf cs = satisfy (`elem` cs)
oneOf = satisfy . flip elem

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

{- https://stepik.org/lesson/30425/step/5?unit=11042 -}

instance Applicative Parser where
  pure :: a -> Parser a
  pure x = Parser $ \s -> [(x, s)]

  (<*>) :: Parser (a -> b) -> Parser a -> Parser b
  (Parser pf) <*> (Parser px) = Parser $ \s -> [(f x, s2) | (f, s1) <- pf s, (x, s2) <- px s1]

testAp :: Bool
testAp = apply ((,) <$> anyChar <*> anyChar) "ABCDE" == [(('A', 'B'), "CDE")]
  && apply (anyChar *> anyChar) "ABCD" == [('B', "CD")]

test :: Bool
test = testAnyChar && testOneOf && testFmap1 && testFmap2 && testAp
