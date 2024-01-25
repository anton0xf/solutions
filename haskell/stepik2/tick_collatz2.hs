{- https://stepik.org/lesson/31556/step/12?unit=11810
3.3.12. Трансформеры монад -}

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Control.Monad.Trans.Except

{- Модифицируйте монаду EsSi из предыдущей задачи, обернув ее в трансформер ReaderT с окружением,
представляющим собой пару целых чисел, задающих нижнюю и верхнюю границы для вычислений.
Функции go теперь не надо будет передавать эти параметры, они будут браться из окружения.
Сделайте получившуюся составную монаду трансформером: -}

type RiiEsSiT m = ReaderT (Integer, Integer) (ExceptT String (StateT Integer m))

{- Реализуйте также функцию для запуска этого трансформера -}

runRiiEsSiT :: RiiEsSiT m a -> (Integer, Integer) -> Integer -> m (Either String a, Integer)
-- runRiiEsSiT m (a, b) n = runStateT (runExceptT $ runReaderT m (a, b)) n
runRiiEsSiT m = runStateT . runExceptT . runReaderT m
-- runRiiEsSiT = runStateT . runExceptT .: runReaderT

-- from composition:Data.Composition
infixr 8 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(f .: g) x y = f (g x y)

{- и модифицируйте код функции go, изменив её тип на -}

go :: Monad m => StateT Integer m Integer -> RiiEsSiT m ()
go step = do
  (a, b) <- ask
  (lift . lift) step
  x <- (lift . lift) get
  when (x <= a) (lift $ throwE "Lower bound")
  when (b <= x) (lift $ throwE "Upper bound")

{- так, чтобы для шага вычисления последовательности с отладочным выводом текущего
элемента последовательности на экран -}

tickCollatzIO :: StateT Integer IO Integer
tickCollatzIO = do
  n <- get
  let res = if odd n then 3 * n + 1 else n `div` 2
  lift $ print res
  put res
  return n

tickCollatzLog :: StateT Integer (Writer [String]) Integer
tickCollatzLog = do
  n <- get
  let res = if odd n then 3 * n + 1 else n `div` 2
  lift $ tell [show res]
  put res
  return n

{- мы получили бы: -}
tickCollatzLogTest :: Bool
tickCollatzLogTest = (runWriter (runRiiEsSiT (forever $ go tickCollatzLog) (1, 200) 27)
                       :: ((Either String Integer, Integer), [String]))
                     == ((Left "Upper bound", 214),
                         ["82", "41", "124", "62", "31", "94", "47", "142", "71", "214"])

-- all tests
test :: Bool
test = tickCollatzLogTest
