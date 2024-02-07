{- https://stepik.org/lesson/38579/step/14?unit=20504
4.2.14. Трансформер StateT -}

import Data.Monoid
import Control.Monad.Trans
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State

{- Те из вас, кто проходил первую часть нашего курса, конечно же помнят, последнюю задачу из него.
В тот раз всё закончилось монадой State, но сейчас с неё все только начинается! -}

data Tree a = Leaf a | Fork (Tree a) a (Tree a)
  deriving (Show, Eq)

{- Вам дано значение типа Tree (), иными словами, вам задана форма дерева. От вас требуется
сделать две вещи:
* во-первых, пронумеровать вершины дерева, обойдя их in-order обходом
  (левое поддерево, вершина, правое поддерево);
* во-вторых, подсчитать количество листьев в дереве. -}

numberAndCountTest :: Bool
numberAndCountTest = numberAndCount (Leaf ()) == (Leaf 1, 1)
  && numberAndCount (Fork (Leaf ()) () (Leaf ())) == (Fork (Leaf 1) 2 (Leaf 3), 2)

{- Конечно, можно решить две подзадачи по-отдельности, но мы сделаем это всё за один проход.
Если бы вы писали решение на императивном языке, вы бы обошли дерево, поддерживая в одной
переменной следующий доступный номер для очередной вершины, а в другой — количество встреченных
листьев, причем само значение второй переменной, по сути, в процессе обхода не требуется.
Значит, вполне естественным решением будет завести состояние для первой переменной,
а количество листьев накапливать в «логе»-моноиде.

Вот так выглядит код, запускающий наше вычисление и извлекающий результат: -}

numberAndCount :: Tree () -> (Tree Integer, Integer)
numberAndCount t = getSum <$> runWriter (evalStateT (go t) 1)
  where go :: Tree () -> StateT Integer (Writer (Sum Integer)) (Tree Integer)
        go (Leaf _) = do
            n <- getAndModyfy (+1)
            lift $ tell 1
            return $ Leaf n
        go (Fork t1 _ t2) = do
            t1' <- go t1
            n <- getAndModyfy (+1)
            t2' <- go t2
            return $ Fork t1' n t2'

getAndModyfy :: Monad m => (s -> s) -> StateT s m s
getAndModyfy f = do
  st <- get
  modify f
  return st

test :: Bool
test = numberAndCountTest
