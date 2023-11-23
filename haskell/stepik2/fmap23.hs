{- https://stepik.org/lesson/28880/step/5?unit=9912

1.1.5. Определение аппликативного функтора

Сделайте типы данных Arr2 e1 e2 и Arr3 e1 e2 e3 представителями класса типов Functor: -}

newtype Arr2 e1 e2 a = Arr2 { getArr2 :: e1 -> e2 -> a }

newtype Arr3 e1 e2 e3 a = Arr3 { getArr3 :: e1 -> e2 -> e3 -> a }

{- Эти типы инкапсулируют вычисление с двумя и тремя независимыми окружениями соответственно: -}

instance Functor (Arr2 e1 e2) where
  fmap :: (a -> b) -> Arr2 e1 e2 a -> Arr2 e1 e2 b
  fmap f arr = Arr2 $ \e1 e2 -> f $ getArr2 arr e1 e2

testArr2 :: Bool
testArr2 = getArr2 (fmap length (Arr2 take)) 10 "abc" == 3
  && getArr2 (fmap length (Arr2 take)) 10 (replicate 15 "a") == 10

instance Functor (Arr3 e1 e2 e3) where
  fmap :: (a -> b) -> Arr3 e1 e2 e3 a -> Arr3 e1 e2 e3 b
  fmap f arr = Arr3 $ \e1 e2 e3 -> f $ getArr3 arr e1 e2 e3

testArr3 :: Bool
testArr3 = getArr3 (tail <$> tail <$> Arr3 zipWith)
    (+) [1, 2, 3, 4] [10, 20, 30, 40, 50]
  == [33,44]

test :: Bool
test = testArr2 && testArr3
