{- https://stepik.org/lesson/31556/step/11?unit=11810
3.3.11. Трансформеры монад -}

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Except

{- Предположим мы хотим исследовать свойства рекуррентных последовательностей.
Рекуррентные отношения будем задавать вычислениями типа State Integer Integer, которые,
будучи инициализированы текущим значением элемента последовательности,
возвращают следующее значение в качестве состояния и текущее в качестве возвращаемого значения,
например: -}

tickCollatz :: State Integer Integer
tickCollatz = do
  n <- get
  let res = if odd n then 3 * n + 1 else n `div` 2
  put res
  return n

{- Используя монаду State из модуля Control.Monad.Trans.State и трансформер ExceptT
из модуля Control.Monad.Trans.Except библиотеки transformers, реализуйте для монады -}

type EsSi = ExceptT String (State Integer)

{- функцию runEsSi :: EsSi a -> Integer -> (Either String a, Integer), запускающую вычисление
в этой монаде, а также функцию go :: Integer -> Integer -> State Integer Integer -> EsSi (),
принимающую шаг рекуррентного вычисления и два целых параметра, задающие нижнюю и верхнюю границы
допустимых значений вычислений. Если значение больше или равно верхнему или меньше или равно
нижнему, то оно прерывается исключением с соответствующим сообщением об ошибке -}

tickCollatzTest :: Bool
tickCollatzTest = runEsSi (go 1 85 tickCollatz) 27 == (Right (), 82)
  && runEsSi (go 1 80 tickCollatz) 27 == (Left "Upper bound", 82)
  && runEsSi (forever $ go 1 1000 tickCollatz :: EsSi Integer) 27 == (Left "Upper bound", 1186)
  && runEsSi (forever $ go 1 10000 tickCollatz :: EsSi Integer) 27 == (Left "Lower bound", 1)

-- solution
runEsSi :: EsSi a -> Integer -> (Either String a, Integer)
-- runEsSi m n = runState (runExceptT m) n
runEsSi = runState . runExceptT

go :: Integer -> Integer -> State Integer Integer -> EsSi ()
go a b step = do
  lift step
  x <- lift get
  when (x <= a) (throwE "Lower bound")
  when (b <= x) (throwE "Upper bound")

-- all tests
test :: Bool
test = tickCollatzTest
