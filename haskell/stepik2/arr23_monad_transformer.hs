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

{- https://stepik.org/lesson/38577/step/6?unit=17396
3.4.6. Трансформер ReaderT
Сделайте трансформеры Arr2T и Arr3T представителями класса типов Functor в предположении,
что m является функтором -}

instance Functor m => Functor (Arr2T e1 e2 m) where
  fmap :: (a -> b) -> Arr2T e1 e2 m a -> Arr2T e1 e2 m b
  fmap f = Arr2T . (\g e1 e2 -> f <$> g e1 e2) . getArr2T

arr2FmapTest :: Bool
arr2FmapTest = (getArr2T $ succ <$> a2l) 10 100 == [11, 101, 111]
  where a2l = Arr2T $ \e1 e2 -> [e1, e2, e1 + e2]

instance Functor m => Functor (Arr3T e1 e2 e3 m) where
  fmap :: (a -> b) -> Arr3T e1 e2 e3 m a -> Arr3T e1 e2 e3 m b
  fmap f = Arr3T . (\g e1 e2 e3 -> f <$> g e1 e2 e3) . getArr3T

arr3FmapTest :: Bool
arr3FmapTest = (getArr3T $ sqrt <$> a3e) 2 3 4 == Right 3.0
  where a3e = Arr3T $ \e1 e2 e3 -> (Right (e1 + e2 + e3) :: Either String Double)

{- https://stepik.org/lesson/38577/step/10?unit=17396
3.4.10. Трансформер ReaderT
Сделайте трансформеры Arr2T и Arr3T представителями класса типов Applicative в предположении,
что m является аппликативным функтором -}

instance Applicative m => Applicative (Arr2T e1 e2 m) where
  pure :: a -> Arr2T e1 e2 m a
  pure x = Arr2T (\e1 e2 -> pure x)

  (<*>) :: Arr2T e1 e2 m (a -> b) -> Arr2T e1 e2 m a -> Arr2T e1 e2 m b
  (Arr2T rf) <*> (Arr2T rx) = Arr2T (\e1 e2 -> rf e1 e2 <*> rx e1 e2)

instance Applicative m => Applicative (Arr3T e1 e2 e3 m) where
  pure :: a -> Arr3T e1 e2 e3 m a
  pure x = Arr3T (\e1 e2 e3 -> pure x)

  (<*>) :: Arr3T e1 e2 e3 m (a -> b) -> Arr3T e1 e2 e3 m a -> Arr3T e1 e2 e3 m b
  (Arr3T rf) <*> (Arr3T rx) = Arr3T (\e1 e2 e3 -> rf e1 e2 e3 <*> rx e1 e2 e3)

apArr2Test :: Bool
apArr2Test = getArr2T (a2fl <*> a2l) 2 10 == [22, 30, 7, 7]
  where a2l = Arr2T $ \e1 e2 -> [e1,e2]
        a2fl = Arr2T $ \e1 e2 -> [(e1 * e2 +), const 7]

apArr3Test :: Bool
apArr3Test = getArr3T (a3fl <*> a3l) 3 5 7 == [8, 10, 10, 12]
  where a3fl = Arr3T $ \e1 e2 e3 -> [(e2+),(e3+)]
        a3l = Arr3T $ \e1 e2 e3 -> [e1,e2]

-- all tests
test :: Bool
test = arr2Test && arr3Test
  && arr2FmapTest && arr3FmapTest
  && apArr2Test && apArr3Test
