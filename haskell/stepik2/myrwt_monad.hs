{- https://stepik.org/lesson/31556/step/9?unit=11810
3.3.9. Трансформеры монад -}

import Data.Char
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

test :: Bool
test = logFirstAndRetSecondTest
