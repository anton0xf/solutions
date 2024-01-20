{- https://stepik.org/lesson/31556/step/2?unit=11810
3.3.2. Трансформеры монад -}

import Data.Char
import Data.Monoid
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer

secondElem :: Reader [String] String
secondElem = asks (map toUpper . head . tail)

strs :: [String]
strs = ["abc", "defg", "qwer", "asdf"]

secondElemTest :: Bool
secondElemTest = runReader secondElem strs == "DEFG"

logFirst :: [String] -> Writer String String
logFirst xs = do
  tell $ head xs
  return $ map toUpper $ head $ tail xs

logFirstTest :: Bool
logFirstTest = runWriter (logFirst strs) == ("DEFG", "abc")

{- https://stepik.org/lesson/31556/step/3?unit=11810
3.3.3. Трансформеры монад -}

logFirstAndRetSecond1 :: ReaderT [String] (Writer String) String
logFirstAndRetSecond1 = do
  e1 <- asks head
  e2 <- asks (map toUpper . head . tail)
  lift $ tell e1
  return e2

logFirstAndRetSecond1Test :: Bool
logFirstAndRetSecond1Test = runWriter (runReaderT logFirstAndRetSecond1 strs) == ("DEFG", "abc")

{- https://stepik.org/lesson/31556/step/4?unit=11810
3.3.4. Трансформеры монад -}

{- Перепишите функцию logFirstAndRetSecond из предыдущего видео,
используя трансформер WriterT из модуля Control.Monad.Trans.Writer
библиотеки transformers, и монаду Reader в качестве базовой. -}

logFirstAndRetSecond2 :: WriterT String (Reader [String]) String
logFirstAndRetSecond2 = do
  e1 <- lift $ asks head
  e2 <- lift $ asks (map toUpper . head . tail)
  tell e1
  return e2

logFirstAndRetSecond2Test :: Bool
logFirstAndRetSecond2Test = runReader (runWriterT logFirstAndRetSecond2) strs == ("DEFG","abc")

-- list with reader example
{- HLINT ignore "Use <$>" -}
plusAndMult0 :: Int -> [Int]
plusAndMult0 n = do
  f <- [(+ n), (* n)]
  x <- [0..3]
  return $ f x

plusAndMult0Test :: Bool
plusAndMult0Test = plusAndMult0 3 == [3, 4, 5, 6, 0, 3, 6, 9]

plusAndMult1 :: ReaderT Int [] Int
plusAndMult1 = do
  n <- ask
  f <- lift [(+ n), (* n)]
  x <- lift [0..3]
  return $ f x

plusAndMult1Test :: Bool
plusAndMult1Test = runReaderT plusAndMult1 3 == [3, 4, 5, 6, 0, 3, 6, 9]

-- list with writer example
plusAndMult2 :: Int -> WriterT [String] [] Int
plusAndMult2 n = do
  f <- lift [(+ n), (* n)]
  x <- lift [0..3]
  let res = f x
  tell [show x ++ " -> " ++ show res]
  return res

plusAndMult2Test :: Bool
plusAndMult2Test = (runWriter . mapM writer . runWriterT . plusAndMult2) 3
  == ([      3,        4,        5,        6,        0,        3,        6,        9],
      ["0 -> 3", "1 -> 4", "2 -> 5", "3 -> 6", "0 -> 0", "1 -> 3", "2 -> 6", "3 -> 9"])

{- https://stepik.org/lesson/31556/step/5?unit=11810
3.3.5. Трансформеры монад

Реализуйте функцию separate. Эта функция принимает два предиката и список и записывает
в один лог элементы списка, удовлетворяющие первому предикату, в другой лог — второму предикату,
а возвращающает список элементов, ни одному из них не удовлетворяющих. -}

separate :: (a -> Bool) -> (a -> Bool) -> [a] -> WriterT [a] (Writer [a]) [a]
separate _ _ [] = return []
separate p1 p2 (x : xs)
  | p1 x = do tell [x]
              separate p1 p2 xs
  | p2 x = do lift $ tell [x]
              separate p1 p2 xs
  | otherwise = (x :) <$> separate p1 p2 xs

separateTest :: Bool
separateTest = (runWriter . runWriterT) (separate (<3) (>7) [0..10])
  == (([3, 4, 5, 6, 7], [0, 1, 2]), [8, 9, 10])

-- example of two writers with different log types
twoWriters :: WriterT (Sum Int) (Writer [Bool]) String
twoWriters = do
  tell $ Sum 1
  lift $ tell [True]
  tell $ Sum 2
  lift $ tell [False]
  return "OK"

twoWritersTest = (runWriter. runWriterT) twoWriters == (("OK", Sum 3), [True, False])

-- all tests
test :: Bool
test = secondElemTest && logFirstTest
  && logFirstAndRetSecond1Test && logFirstAndRetSecond2Test
  && plusAndMult0Test && plusAndMult1Test && plusAndMult2Test
  && separateTest && twoWritersTest
