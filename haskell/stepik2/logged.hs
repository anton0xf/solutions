{- https://stepik.org/lesson/38578/step/7?unit=20503
4.1.7. Трансформер WriterT -}

import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Fail
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Class

{- Сделайте на основе типа данных -}

data Logged a = Logged String a
  deriving (Eq, Show)

instance Functor Logged where
  fmap :: (a -> b) -> Logged a -> Logged b
  fmap f (Logged log x) = Logged log (f x)

instance Applicative Logged where
  pure :: a -> Logged a
  pure = Logged ""

  (<*>) :: Logged (a -> b) -> Logged a -> Logged b
  (Logged log1 f) <*> (Logged log2 x) = Logged (log1 ++ log2) (f x)

{- трансформер монад LoggT :: (* -> *) -> * -> *
с одноименным конструктором данных и меткой поля runLoggT: -}

newtype LoggT m a = LoggT { runLoggT :: m (Logged a) }

{- Для этого реализуйте для произвольной монады m представителя
класса типов Monad для LoggT m :: * -> *: -}

instance Functor m => Functor (LoggT m) where
  fmap :: (a -> b) -> LoggT m a -> LoggT m b
  fmap f = LoggT . (fmap . fmap) f . runLoggT

instance Applicative m => Applicative (LoggT m) where
  pure :: a -> LoggT m a
  pure = LoggT . pure . pure

  (<*>) :: LoggT m (a -> b) -> LoggT m a -> LoggT m b
  (LoggT lf) <*> (LoggT lx) = LoggT $ liftA2 (<*>) lf lx

instance Monad m => Monad (LoggT m) where
  (>>=) :: LoggT m a -> (a -> LoggT m b) -> LoggT m b
  (LoggT lx) >>= k = LoggT $ do
    (Logged log1 x) <- lx
    (Logged log2 y) <- runLoggT (k x)
    return $ Logged (log1 ++ log2) y

instance MonadFail m => MonadFail (LoggT m) where
  fail :: String -> LoggT m a
  fail = LoggT . fail

{- Для проверки используйте функции: -}

logTst :: LoggT Identity Integer
logTst = do 
  x <- LoggT $ Identity $ Logged "AAA" 30
  let y = 10
  z <- LoggT $ Identity $ Logged "BBB" 2
  return $ x + y + z
  
failTst :: [Integer] -> LoggT [] Integer
failTst xs = do
  5 <- LoggT $ fmap (Logged "") xs
  LoggT [Logged "A" ()]
  return 42

{- которые при правильной реализации монады должны вести себя так: -}

loggTTest = runIdentity (runLoggT logTst) == Logged "AAABBB" 42
  && runLoggT (failTst [5,5]) == [Logged "A" 42,Logged "A" 42]
  && runLoggT (failTst [5,6]) == [Logged "A" 42]
  && null (runLoggT $ failTst [7,6])

{- https://stepik.org/lesson/38578/step/10?unit=20503
4.1.10. Трансформер WriterT

Напишите функцию write2log обеспечивающую трансформер LoggT стандартным логгирующим интерфейсом: -}

write2log :: Monad m => String -> LoggT m ()
write2log msg = LoggT $ return $ Logged msg ()

{- Эта функция позволяет пользователю осуществлять запись в лог в процессе вычисления в монаде
LoggT m для любой монады m. Введите для удобства упаковку для LoggT Identity и напишите функцию
запускающую вычисления в этой монаде -}

type Logg = LoggT Identity

runLogg :: Logg a -> Logged a
runLogg = runIdentity . runLoggT

{- Тест -}

logTst' :: Logg Integer
logTst' = do
  write2log "AAA"
  write2log "BBB"
  return 42

{- должен дать такой результат: -}

loggTest :: Bool
loggTest = runLogg logTst' == Logged "AAABBB" 42

{- А тест (подразумевающий импорт Control.Monad.Trans.State и Control.Monad.Trans.Class) -}

stLog :: StateT Integer Logg Integer
stLog = do
  modify (+1)
  a <- get
  lift $ write2log $ show $ a * 10
  put 42
  return $ a * 100

{- такой: -}

stLogTest :: Bool
stLogTest = runLogg (runStateT stLog 2) == Logged "30" (300, 42)


{- https://stepik.org/lesson/38578/step/12?unit=20503 -}
instance MonadTrans LoggT where
  lift :: Monad m => m a -> LoggT m a
  lift = LoggT . (Logged mempty <$>)

-- all tests
test :: Bool
test = loggTTest && loggTest && stLogTest
