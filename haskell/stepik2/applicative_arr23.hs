{- https://stepik.org/lesson/30424/step/10?unit=11041
1.2.10. Представители класса типов Applicative

Сделайте типы данных Arr2 e1 e2 и Arr3 e1 e2 e3 представителями класса типов Applicative -}

newtype Arr2 e1 e2 a = Arr2 { getArr2 :: e1 -> e2 -> a }

newtype Arr3 e1 e2 e3 a = Arr3 { getArr3 :: e1 -> e2 -> e3 -> a }

{- с естественной семантикой двух и трех окружений: -}

testArr2 :: Bool
testArr2 = getArr2 (Arr2 (\x y z -> x + y - z) <*> Arr2 (*)) 2 3 == -1

testArr3 :: Bool
testArr3 = getArr3 (Arr3 (\x y z w -> x + y + z - w)
                    <*> Arr3 (\x y z -> x * y * z)) 2 3 4
  == -15

-- from fmap23.hs
instance Functor (Arr2 e1 e2) where
  fmap :: (a -> b) -> Arr2 e1 e2 a -> Arr2 e1 e2 b
  fmap f = Arr2 . (fmap . fmap $ f) . getArr2

instance Applicative (Arr2 e1 e2) where
  pure :: a -> Arr2 e1 e2 a
  pure x = Arr2 $ const . const x

{-
const :: a -> b -> a
const (x :: a) :: c -> a
(.) :: (b' -> c') -> (a' -> b') -> a' -> c'
-- b' = a
-- c' = b -> a
-- a' = c
-- b' = x = a
(.) :: (a -> b -> a) -> (c -> a) -> c -> b -> a
-}


-- from fmap23.hs
instance Functor (Arr3 e1 e2 e3) where
  fmap :: (a -> b) -> Arr3 e1 e2 e3 a -> Arr3 e1 e2 e3 b
  fmap f = Arr3 . (fmap . fmap . fmap $ f) . getArr3

instance Applicative (Arr3 e1 e2 e3) where

test :: Bool
test = testArr2 && testArr3
