{- https://stepik.org/lesson/38577/step/3?unit=17396
3.4.3. Трансформер ReaderT -}

import Data.Functor.Identity
import Control.Applicative
import Control.Monad.Fail
import Control.Monad.Trans

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
  -- fmap f = Arr2T . (\g e1 e2 -> f <$> g e1 e2) . getArr2T
  fmap f = Arr2T . (fmap . fmap . fmap $ f) . getArr2T

arr2FmapTest :: Bool
arr2FmapTest = (getArr2T $ succ <$> a2l) 10 100 == [11, 101, 111]
  where a2l = Arr2T $ \e1 e2 -> [e1, e2, e1 + e2]

instance Functor m => Functor (Arr3T e1 e2 e3 m) where
  fmap :: (a -> b) -> Arr3T e1 e2 e3 m a -> Arr3T e1 e2 e3 m b
  -- fmap f = Arr3T . (\g e1 e2 e3 -> f <$> g e1 e2 e3) . getArr3T
  fmap f = Arr3T . (fmap . fmap . fmap . fmap $ f) . getArr3T

arr3FmapTest :: Bool
arr3FmapTest = (getArr3T $ sqrt <$> a3e) 2 3 4 == Right 3.0
  where a3e = Arr3T $ \e1 e2 e3 -> (Right (e1 + e2 + e3) :: Either String Double)

{- https://stepik.org/lesson/38577/step/10?unit=17396
3.4.10. Трансформер ReaderT
Сделайте трансформеры Arr2T и Arr3T представителями класса типов Applicative в предположении,
что m является аппликативным функтором -}

instance Applicative m => Applicative (Arr2T e1 e2 m) where
  pure :: a -> Arr2T e1 e2 m a
  -- pure x = Arr2T (\e1 e2 -> pure x)
  pure = Arr2T . const . const . pure

  (<*>) :: Arr2T e1 e2 m (a -> b) -> Arr2T e1 e2 m a -> Arr2T e1 e2 m b
  -- (Arr2T rf) <*> (Arr2T rx) = Arr2T (\e1 e2 -> rf e1 e2 <*> rx e1 e2)
  (Arr2T rf) <*> (Arr2T rx) = Arr2T $ (liftA2 . liftA2) (<*>) rf rx

instance Applicative m => Applicative (Arr3T e1 e2 e3 m) where
  pure :: a -> Arr3T e1 e2 e3 m a
  -- pure x = Arr3T (\e1 e2 e3 -> pure x)
  pure = Arr3T . const . const . const . pure

  (<*>) :: Arr3T e1 e2 e3 m (a -> b) -> Arr3T e1 e2 e3 m a -> Arr3T e1 e2 e3 m b
  -- (Arr3T rf) <*> (Arr3T rx) = Arr3T (\e1 e2 e3 -> rf e1 e2 e3 <*> rx e1 e2 e3)
  (Arr3T rf) <*> (Arr3T rx) = Arr3T $ (liftA2 . liftA2 . liftA2) (<*>) rf rx

apArr2Test :: Bool
apArr2Test = getArr2T (a2fl <*> a2l) 2 10 == [22, 30, 7, 7]
  where a2l = Arr2T $ \e1 e2 -> [e1,e2]
        a2fl = Arr2T $ \e1 e2 -> [(e1 * e2 +), const 7]

apArr3Test :: Bool
apArr3Test = getArr3T (a3fl <*> a3l) 3 5 7 == [8, 10, 10, 12]
  where a3fl = Arr3T $ \e1 e2 e3 -> [(e2+),(e3+)]
        a3l = Arr3T $ \e1 e2 e3 -> [e1,e2]

{- https://stepik.org/lesson/38577/step/12?unit=17396
3.4.12. Трансформер ReaderT
Сделайте трансформеры Arr2T и Arr3T представителями класса типов Monad в предположении,
что m является монадой -}

instance Monad m => Monad (Arr2T e1 e2 m) where
  (>>=) :: Arr2T e1 e2 m a -> (a -> Arr2T e1 e2 m b) -> Arr2T e1 e2 m b
  -- (Arr2T rx) >>= k = Arr2T $ \e1 e2 -> rx e1 e2 >>= (\m -> getArr2T m e1 e2) . k
  (Arr2T rx) >>= k = Arr2T $ \e1 e2 -> do
    x <- rx e1 e2
    getArr2T (k x) e1 e2

instance Monad m => Monad (Arr3T e1 e2 e3 m) where
  (>>=) :: Arr3T e1 e2 e3 m a -> (a -> Arr3T e1 e2 e3 m b) -> Arr3T e1 e2 e3 m b
  -- (Arr3T rx) >>= k = Arr3T $ \e1 e2 e3 -> rx e1 e2 e3 >>= (\m -> getArr3T m e1 e2 e3) . k
  (Arr3T rx) >>= k = Arr3T $ \e1 e2 e3 -> do
    x <- rx e1 e2 e3
    getArr3T (k x) e1 e2 e3

monadArr2Test :: Bool
monadArr2Test = getArr2T (do {x <- a2l; y <- a2l; return (x + y)}) 3 5 == [6, 8, 8, 10]
  where a2l = Arr2T $ \e1 e2 -> [e1,e2]

monadArr3Test :: Bool
monadArr3Test = getArr3T (do {x <- a3m; y <- a3m; return (x * y)}) 2 3 4 == Just 81
  where a3m = Arr3T $ \e1 e2 e3 -> Just (e1 + e2 + e3)

-- MonadTrans
instance MonadTrans (Arr2T e1 e2) where
  lift :: Monad m => m a -> Arr2T e1 e2 m a
  lift = Arr2T . const . const

instance MonadTrans (Arr3T e1 e2 e3) where
  lift :: Monad m => m a -> Arr3T e1 e2 e3 m a
  lift = Arr3T . const . const . const

{- https://stepik.org/lesson/38577/step/13?unit=17396
3.4.13. Трансформер ReaderT
Разработанная нами реализация интерфейса монады для трансформера Arr3T (как и для Arr2T и ReaderT)
имеет не очень хорошую особенность. При неудачном сопоставлении с образцом вычисления в этой
монаде завершаются аварийно, с выводом сообщения об ошибке в диагностический поток:

GHCi> a3m = Arr3T $ \e1 e2 e3 -> Just (e1 + e2 + e3)
GHCi> getArr3T (do {9 <- a3m; y <- a3m; return y}) 2 3 4
Just 9
GHCi> getArr3T (do {10 <- a3m; y <- a3m; return y}) 2 3 4
*** Exception: Pattern match failure in do expression at :12:15-16

Для обычного ридера такое поведение нормально, однако у трансформера внутренняя монада может
уметь обрабатывать ошибки более щадащим образом. Переопределите функцию fail класса типов Monad
для Arr3T так, чтобы обработка неудачного сопоставления с образцом осуществлялась
бы во внутренней монаде -}

instance MonadFail m => MonadFail (Arr2T e1 e2 m) where
  fail :: String -> Arr2T e1 e2 m a
  -- fail msg = Arr2T $ \e1 e2 -> fail msg
  -- fail = Arr2T . const . const . fail
  fail = lift . fail

instance MonadFail m => MonadFail (Arr3T e1 e2 e3 m) where
  fail :: String -> Arr3T e1 e2 e3 m a
  -- fail msg = Arr3T $ \e1 e2 e3 -> fail msg
  -- fail = Arr3T . const . const . const . fail
  fail = lift . fail

failArr3Test :: Bool
failArr3Test = getArr3T (do { 10 <- a3m; a3m }) 2 3 4 == (Nothing :: Maybe Int)
               && getArr3T (do { 9 <- a3m; a3m }) 2 3 4 == Just 9
  where a3m = Arr3T $ \e1 e2 e3 -> Just (e1 + e2 + e3)

-- all tests
test :: Bool
test = arr2Test && arr3Test
  && arr2FmapTest && arr3FmapTest
  && apArr2Test && apArr3Test
  && monadArr2Test && monadArr3Test
  && failArr3Test
