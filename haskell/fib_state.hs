{- https://stepik.org/lesson/8444/step/9?unit=1579
Если бы мы хотели вычислить nn-е число Фибоначчи на императивном языке программирования,
мы бы делали это с помощью двух переменных и цикла, обновляющего эти переменные:

def fib(n):
  a, b = 0, 1
  for i in [1 .. n]:
    a, b = b, a + b
  return a

С точки зрения Хаскеля, такую конструкцию удобно представлять себе как вычисление с состоянием.
Состояние в данном случае — это два целочисленных значения. -}

import Control.Monad

newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State m) = State $ \s -> let (x, s1) = m s
                                   in (f x, s1)
instance Applicative (State s) where
  pure :: a -> State s a
  pure x = State (x,)
  
  (<*>) :: State s (a -> b) -> State s a -> State s b
  (State sf) <*> (State sx) = State $ \s ->
    let (f, s1) = sf s
        (x, s2) = sx s1
    in (f x, s2)

instance Monad (State s) where
  (>>=) :: State s a -> (a -> State s b) -> State s b
  (State sx) >>= k = State $ \s ->
    let (x, s1) = sx s
        State sy = k x
    in sy s1

execState :: State s a -> s -> s
execState m s = snd $ runState m s

evalState :: State s a -> s -> a
evalState m s = fst $ runState m s

get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ const ((), s)

modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((), f s)

{- Императивный алгоритм действует очень просто: он совершает nn шагов, каждый из которых некоторым
образом изменяет текущее состояние. Первым делом, реализуйте функцию fibStep,
изменяющую состояние таким же образом, как и один шаг цикла в императивном алгоритме: -}

fibStep :: State (Integer, Integer) ()
fibStep = do
  (a, b) <- get
  put (b, a + b)

testFibStep :: Bool
testFibStep = execState fibStep (0, 1) == (1, 1)
  && execState fibStep (1, 1) == (1, 2)
  && execState fibStep (1, 2) == (2, 3)

{- После этого останется лишь применить этот шаг nn раз к правильному стартовому состоянию и выдать
ответ. Реализуйте вспомогательную функцию execStateN, которая принимает число шагов n, вычисление
с состоянием и начальное состояние, запускает вычисление n раз и выдает получившееся состояние
(игнорируя сами результаты вычислений). Применяя эту функцию к fibStep, мы сможем вычислять
числа Фибоначчи: -}

execStateN :: Int -> State s a -> s -> s
execStateN n m = execState $ replicateM_ n m

fib :: Int -> Integer
fib n = fst $ execStateN n fibStep (0, 1)

testFib :: Bool
testFib = map fib [1..5] == [1, 1, 2, 3, 5]

test :: Bool
test = testFibStep && testFib
