{- https://stepik.org/lesson/45331/step/6?unit=23645
4.5.6. Задачи на трансформеры -}

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
import Data.Bifunctor
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable

{- Чтобы закончить наш курс ярко, предлагаем вам с помощью этой задачи в полной мере почувствовать
на себе всю мощь continuation-passing style. Чтобы успешно решить эту задачу, вам нужно хорошо
понимать, как работает CPS и монада ContT (а этого, как известно, никто не понимает).
Кстати, это была подсказка.

Сопрограмма (корутина, coroutine) это обобщение понятия подпрограммы (по-простому говоря, функции).
У функции, в отличие от сопрограммы, есть одна точка входа (то, откуда она начинает работать),
а точек выхода может быть несколько, но выйти через них функция может только один раз за время
работы; у сопрограммы же точек входа и выхода может быть несколько.
Проще всего объяснить на примере: -}

coroutine1 :: CoroutineT (Writer String) ()
coroutine1 = do
  tell "1"
  yield
  tell "2"

coroutine2 :: CoroutineT (Writer String) ()
coroutine2 = do
  tell "a"
  yield
  tell "b"

test1 :: Bool
test1 = execWriter (runCoroutines coroutine1 coroutine2) == "1a2b"

{- Здесь используется специальное действие yield, которое передает управление другой сопрограмме.
Когда другая сопрограмма возвращает управление (с помощью того же yield или завершившись),
первая сопрограмма продолжает работу с того места, на котором остановилась в прошлый раз.

В общем случае, одновременно могут исполняться несколько сопрограмм, причем при передаче
управления, они могут обмениваться значениями. В этой задаче достаточно реализовать сопрограммы
в упрощенном виде: одновременно работают ровно две сопрограммы и значениями обмениваться
они не могут.

Реализуйте трансформер CoroutineT, функцию yield для передачи управления и функцию runCoroutines
для запуска. Учтите, что одна сопрограмма может завершиться раньше другой;
другая должна при этом продолжить работу: -}

coroutine3, coroutine4 :: CoroutineT (Writer String) ()
coroutine3 = do
  tell "1"
  yield
  yield
  tell "2"

coroutine4 = do
  tell "a"
  yield
  tell "b"
  yield
  tell "c"
  yield
  tell "d"
  yield

test2 :: Bool
test2 = execWriter (runCoroutines coroutine3 coroutine4) == "1ab2cd"

-- solution
newtype CoroutineT m a = CoroutineT { runCoroutineT :: m (Either (CoroutineT m a) a) }

instance Monad m => Functor (CoroutineT m) where
  fmap :: (a -> b) -> CoroutineT m a -> CoroutineT m b
  fmap = liftM

instance Monad m => Applicative (CoroutineT m) where
  pure :: a -> CoroutineT m a
  pure = CoroutineT . return . Right

  (<*>) :: CoroutineT m (a -> b) -> CoroutineT m a -> CoroutineT m b
  (<*>) = ap

instance Monad m => Monad (CoroutineT m) where
  (>>=) :: CoroutineT m a -> (a -> CoroutineT m b) -> CoroutineT m b
  (CoroutineT cx) >>= k = CoroutineT
    $ cx >>= either (return . Left . (>>= k)) (runCoroutineT . k)
  -- cx >>= k = CoroutineT $ do
  --   ex <- runCoroutineT cx
  --   case ex of
  --     Right x -> runCoroutineT $ k x
  --     Left cx' -> return $ Left $ cx' >>= k

type LogCoroutine = CoroutineT (Writer [String])

evalCorEx :: Show a => LogCoroutine a -> (a, [String])
-- evalCorEx m = eval $ runWriter (runCoroutineT m)
--   where eval (Right x, log) = (x, log)
--         eval (Left m', log1) = let (x, log2) = evalCorEx m'
--                                in (x, log1 ++ log2)
evalCorEx = runWriter . runOneCoroutine

coroutineEq :: (Show a, Eq a) => LogCoroutine a -> LogCoroutine a -> Bool
coroutineEq m1 m2 = evalCorEx m1 == evalCorEx m2

kleisliEx :: Show a => a -> LogCoroutine a
kleisliEx x = do { tell [show x]; return x }
  -- CoroutineT $ WriterT $ Identity (Right x, [show x])

kleisliYEx :: (Enum a, Show a) => a -> LogCoroutine a
kleisliYEx x = do
  tell [show x]
  yield
  let x' = succ x
  tell [show x']
  return x'

kleisliEx2 :: (Enum a, Show a) => a -> LogCoroutine a
kleisliEx2 x = do { tell [show x]; return $ succ x }

kleisliEx3 :: (Enum a, Show a) => a -> LogCoroutine a
kleisliEx3 x = do { tell [show x]; return $ succ $ succ x }

leftIdLaw :: (Show a, Eq a) => a -> (a -> LogCoroutine a) -> Bool
leftIdLaw x k = coroutineEq (return x >>= k) (k x)

{- HLINT ignore "Monad law, left identity" -}
leftIdLawTest :: Bool
leftIdLawTest = leftIdLaw 'a' kleisliEx

{- HLINT ignore "Monad law, right identity" -}
rightIdLaw :: (Show a, Eq a) => CoroutineT (Writer [String]) a -> Bool
rightIdLaw m = coroutineEq (m >>= return)  m

rightIdLawTest :: Bool
rightIdLawTest = rightIdLaw (kleisliEx 'a')
  && rightIdLaw (kleisliYEx 'a')

assocLaw :: (Show c, Eq c)
  => LogCoroutine a -> (a -> LogCoroutine b) -> (b -> LogCoroutine c) -> Bool
assocLaw m k h = coroutineEq (m >>= (k >=> h)) ((m >>= k) >>= h)

assocLawTest :: Bool
assocLawTest = assocLaw (kleisliEx 'a') kleisliEx2 kleisliEx3
  && assocLaw (kleisliYEx 'a') kleisliEx2 kleisliEx3
  && assocLaw (kleisliEx 'a') kleisliYEx kleisliEx3
  && assocLaw (kleisliEx 'a') kleisliEx2 kleisliYEx

instance MonadWriter w m => MonadWriter w (CoroutineT m) where
  tell :: w -> CoroutineT m ()
  tell log = CoroutineT $ writer (Right (), log)
  
  listen :: CoroutineT m a -> CoroutineT m (a, w)
  listen (CoroutineT cx) = undefined
  -- CoroutineT $ do
  --   (ec, log) <- listen cx
  --   case ec of
  --     Right x -> return $ Right (x, log)
  --     Left c -> do { tell log; return $ Left $ listen c }

  pass :: CoroutineT m (a, w -> w) -> CoroutineT m a
  pass = undefined

runCoroutines :: Monad m => CoroutineT m () -> CoroutineT m () -> m ()
runCoroutines c1 c2 = do
  e1 <- runCoroutineT c1
  case e1 of
    Right _ -> runOneCoroutine c2
    Left e1' -> runCoroutines c2 e1'

runOneCoroutine :: Monad m => CoroutineT m a -> m a
runOneCoroutine c = do
  e <- runCoroutineT c
  case e of
    Right x -> return x
    Left c' -> runOneCoroutine c'

yield :: Monad m => CoroutineT m ()
yield = CoroutineT $ return $ Left $ return ()

-- tests
lawsTest :: Bool
lawsTest = leftIdLawTest && rightIdLawTest && assocLawTest

test :: Bool
test = test1 && test2 && lawsTest
