{- https://stepik.org/lesson/31556/step/9?unit=11810
3.3.9. Трансформеры монад -}

import Data.Char
import Data.Maybe
import Data.Monoid
import Data.Bifunctor
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer

{- Превратите монаду MyRW в трансформер монад MyRWT: -}

logFirstAndRetSecondIO :: MyRWT IO String
logFirstAndRetSecondIO = do
  el1 <- myAsks head
  myLift $ putStrLn $ "First is " ++ show el1
  el2 <- myAsks (map toUpper . head . tail)
  myLift $ putStrLn $ "Second is " ++ show el2
  myTell el1
  return el2

logFirstAndRetSecondW :: MyRWT (Writer [String]) String
logFirstAndRetSecondW = do
  el1 <- myAsks head
  myLift $ tell ["First is " ++ show el1]
  el2 <- myAsks (map toUpper . head . tail)
  myLift $ tell ["Second is " ++ show el2]
  myTell el1
  return el2

logFirstAndRetSecondTest :: Bool
logFirstAndRetSecondTest = runWriter (runMyRWT logFirstAndRetSecondW ["abc","defg","hij"])
  == (("DEFG","abc"), ["First is \"abc\"", "Second is \"DEFG\""])

-- solution
type MyRWT m = ReaderT [String] (WriterT String m)

runMyRWT :: MyRWT m a -> [String] -> m (a, String)
runMyRWT m env  = runWriterT $ runReaderT m env

myAsks :: Monad m => ([String] -> a) -> MyRWT m a
myAsks = asks

myTell :: Monad m => String -> MyRWT m ()
myTell = lift . tell

myLift :: Monad m => m a -> MyRWT m a
myLift = lift . lift

{- https://stepik.org/lesson/31556/step/10?unit=11810
3.3.10. Трансформеры монад
С помощью трансформера монад MyRWT мы можем написать безопасную версию logFirstAndRetSecond: -}

logFirstAndRetSecondSafe :: MyRWT Maybe String
logFirstAndRetSecondSafe = do
  xs <- myAsk
  case xs of
    (el1 : el2 : _) -> myTell el1 >> return (map toUpper el2)
    _ -> myLift Nothing

logFirstAndRetSecondSafeTest :: Bool
logFirstAndRetSecondSafeTest = runMyRWT logFirstAndRetSecondSafe ["abc", "defg", "hij"]
      == Just ("DEFG", "abc")
  && isNothing (runMyRWT logFirstAndRetSecondSafe ["abc"])

{- Реализуйте безопасную функцию veryComplexComputation, записывающую в лог через запятую первую
строку четной длины и первую строку нечетной длины, а возвращающую пару из второй строки четной
и второй строки нечетной длины, приведенных к верхнему регистру: -}

veryComplexComputationTest :: Bool
veryComplexComputationTest = isNothing (runMyRWT veryComplexComputation ["abc","defg","hij"])
  && runMyRWT veryComplexComputation ["abc", "defg", "hij", "kl"]
      == Just (("KL", "HIJ"), "defg,abc")
  && runMyRWT veryComplexComputation (cycle ["abc", "defg", "hij", "kl"])
      == Just (("KL", "HIJ"), "defg,abc")

{- Подсказка: возможно, полезно будет реализовать функцию myWithReader. -}

-- solution
myAsk :: MyRWT Maybe [String]
myAsk = myAsks id

veryComplexComputation :: MyRWT Maybe (String, String)
veryComplexComputation = do
  strs <- myAsk
  e2 <- case filter (even . length) strs of
    (e1 : e2 : _) -> myTell (e1 ++ ",") >> return e2
    _ -> myLift Nothing
  o2 <- case filter (odd . length) strs of
    (o1 : o2 : _) -> myTell o1 >> return o2
    _ -> myLift Nothing
  return (map toUpper e2, map toUpper o2)

-- all tests
test :: Bool
test = logFirstAndRetSecondTest
  && logFirstAndRetSecondSafeTest && veryComplexComputationTest
