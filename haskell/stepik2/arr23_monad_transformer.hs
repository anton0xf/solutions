{- https://stepik.org/lesson/38577/step/3?unit=17396
3.4.3. Трансформер ReaderT -}

import Data.Functor.Identity

{- В задачах из предыдущих модулей мы сталкивались с типами данных -}

newtype Arr2 e1 e2 a = Arr2 { getArr2 :: e1 -> e2 -> a }
newtype Arr3 e1 e2 e3 a = Arr3 { getArr3 :: e1 -> e2 -> e3 -> a }

{- задающих вычисления с двумя и тремя окружениями соответственно.
Можно расширить их до трансформеров: -}

newtype Arr2T e1 e2 m a = Arr2T { getArr2T :: e1 -> e2 -> m a }
newtype Arr3T e1 e2 e3 m a = Arr3T { getArr3T :: e1 -> e2 -> e3 -> m a }

{- Напишите «конструирующие» функции -}

arr2 :: Monad m => (e1 -> e2 -> a) -> Arr2T e1 e2 m a
arr2 f = Arr2T g
  where g x y = return $ f x y

arr3 :: Monad m => (e1 -> e2 -> e3 -> a) -> Arr3T e1 e2 e3 m a
arr3 f = Arr3T g
  where g x y z = return $ f x y z

{- обеспечивающие следующее поведение -}

arr2Test :: Bool
arr2Test = (getArr2T (arr2 (+)) 33 9 :: [Integer]) == [42]
  && runIdentity (getArr2T (arr2 (+)) 33 9) == 42

arr3Test :: Bool
arr3Test = ((getArr3T $ arr3 foldr) (*) 1 [1..5] :: Either String Integer) == Right 120

-- all tests
test :: Bool
test = arr2Test && arr3Test
