{- https://stepik.org/lesson/31555/step/6?unit=11808 -}

import Data.Foldable

{- 2.3.6. Законы и свойства класса Traversable
Рассмотрим следующий тип данных -}

data OddC a = Un a | Bi a a (OddC a) deriving (Eq, Show)

{- Этот тип представляет собой контейнер-последовательность,
который по построению может содержать только нечетное число элементов: -}

cnt1 :: OddC Int
cnt1 = Un 42

cnt3 :: OddC Int
cnt3 = Bi 1 2 cnt1

cnt5 :: OddC Int
cnt5 = Bi 3 4 cnt3

cnt5Test :: Bool
cnt5Test = cnt5 == Bi 3 4 (Bi 1 2 (Un 42))

cntInf :: OddC Char
cntInf = Bi 'A' 'B' cntInf

{- Сделайте этот тип данных представителем классов типов Functor, Foldable и Traversable: -}

instance Functor OddC where
  fmap :: (a -> b) -> OddC a -> OddC b
  fmap f (Un x) = Un (f x)
  fmap f (Bi x1 x2 xs) = Bi (f x1) (f x2) (fmap f xs)

instance Foldable OddC where
  foldr :: (a -> b -> b) -> b -> OddC a -> b
  foldr f ini (Un x) = f x ini
  foldr f ini (Bi x1 x2 xs) = f x1 $ f x2 $ foldr f ini xs

instance Traversable OddC where
  sequenceA :: (Applicative f) => OddC (f a) -> f (OddC a)
  sequenceA (Un fx) = Un <$> fx
  sequenceA (Bi fx1 fx2 fxs) = Bi <$> fx1 <*> fx2 <*> sequenceA fxs

fmapTest :: Bool
fmapTest = ((+1) <$> cnt5) == Bi 4 5 (Bi 2 3 (Un 43))

toListTest :: Bool
toListTest = toList cnt5 == [3,4,1,2,42]

sumTest :: Bool
sumTest = sum cnt5 == 52

traverseTest :: Bool
traverseTest = traverse (\x->[x+2,x-2]) cnt1 == [Un 44,Un 40]

{- https://stepik.org/lesson/28881/step/10?unit=9913
2.4.10. Связь классов Monad и Applicative
Для типа данных OddC реализуйте функцию конкатенирующую три таких контейнера в один.
Обратите внимание, что соображения четности запрещают конкатенацию двух контейнеров OddC -}

concat3OC :: OddC a -> OddC a -> OddC a -> OddC a
concat3OC (Bi x1 x2 xs) ys zs = Bi x1 x2 $ concat3OC xs ys zs
concat3OC (Un x) (Bi y1 y2 ys) zs = Bi x y1 $ concat3OC (Un y2) ys zs
concat3OC (Un x) (Un y) zs = Bi x y zs

tst1 :: OddC Char
tst1 = Bi 'a' 'b' (Un 'c')

tst2 :: OddC Char
tst2 = Bi 'd' 'e' (Bi 'f' 'g' (Un 'h'))

tst3 :: OddC Char
tst3 = Bi 'i' 'j' (Un 'k')

concat3OCTest :: Bool
concat3OCTest = concat3OC tst1 tst2 tst3
  == Bi 'a' 'b' (Bi 'c' 'd' (Bi 'e' 'f' (Bi 'g' 'h' (Bi 'i' 'j' (Un 'k')))))

{- https://stepik.org/lesson/28881/step/11?unit=9913
2.4.11. Связь классов Monad и Applicative
Для типа данных OddC реализуйте функцию concatOC.
Она должна обеспечивать для типа OddC поведение,
аналогичное поведению функции concat для списков -}

concatOC :: OddC (OddC a) -> OddC a
concatOC (Un xs) = xs
concatOC (Bi (Bi x1 x2 xs) ys zss) = Bi x1 x2 $ concatOC (Bi xs ys zss)
concatOC (Bi (Un x) (Bi y1 y2 ys) zss) = Bi x y1 $ concatOC (Bi (Un y2) ys zss)
concatOC (Bi (Un x) (Un y) (Un zs)) = Bi x y zs
concatOC (Bi (Un x) (Un y) zss) = Bi x y $ concatOC zss

concatOCTest :: Bool
concatOCTest = concatOC (Un (Un 42)) == Un 42
  && concatOC (Bi tst1 tst2 (Un tst3))
      == Bi 'a' 'b' (Bi 'c' 'd' (Bi 'e' 'f' (Bi 'g' 'h' (Bi 'i' 'j' (Un 'k')))))

test :: Bool
test = cnt5Test && fmapTest && toListTest && sumTest && traverseTest
  && concat3OCTest && concatOCTest
