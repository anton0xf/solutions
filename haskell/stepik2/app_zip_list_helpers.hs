{- https://stepik.org/lesson/30424/step/5?unit=11041
1.2.5. Представители класса типов Applicative -}

import Control.Applicative (ZipList(ZipList), getZipList)
import Data.List (zipWith4)

{- В модуле Data.List имеется семейство функций zipWith, zipWith3, zipWith4,..: -}
x1s :: [Int]
x1s = [1, 2, 3]

x2s :: [Int]
x2s = [4, 5, 6]

x3s :: [Int]
x3s = [7, 8, 9]

x4s :: [Int]
x4s = [10, 11, 12]

testZipWith2 :: Bool
testZipWith2 = zipWith (\a b -> 2*a+3*b) x1s x2s == [14, 19, 24]

testZipWith3 :: Bool
testZipWith3 = zipWith3 (\a b c -> 2*a+3*b+5*c) x1s x2s x3s == [49, 59, 69]

testZipWith4 :: Bool
testZipWith4 = zipWith4 (\a b c d -> 2*a+3*b+5*c-4*d) x1s x2s x3s x4s == [9, 15, 21]

{- Аппликативные функторы могут заменить всё это семейство -}
testAppZip2 :: Bool
testAppZip2 = getZipList ((\a b -> 2*a+3*b) <$> ZipList x1s <*> ZipList x2s) == [14, 19, 24]

testAppZip3 :: Bool
testAppZip3 = getZipList ((\a b c -> 2*a+3*b+5*c)
                <$> ZipList x1s <*> ZipList x2s <*> ZipList x3s)
              == [49, 59, 69]

testAppZip4 :: Bool
testAppZip4 = getZipList ((\a b c d -> 2*a+3*b+5*c-4*d)
                <$> ZipList x1s <*> ZipList x2s <*> ZipList x3s <*> ZipList x4s)
              == [9, 15, 21]

{- Реализуйте операторы (>*<) и (>$<), позволяющие спрятать упаковку ZipList
и распаковку getZipList: -}

infixl 4 >$<
(>$<) :: (a -> b) -> [a] -> [b]
-- f >$< xs = map f xs
f >$< xs = getZipList $ f <$> ZipList xs
-- f >$< xs = getZipList $ pure f <*> ZipList xs

infixl 4 >*<
(>*<) :: [a -> b] -> [a] -> [b]
-- fs >*< ys = zipWith ($) fs ys
fs >*< ys = getZipList $ ZipList fs <*> ZipList ys

testHelpers1 :: Bool
testHelpers1 = ((*2) >$< x1s) == [2, 4, 6]

testHelpers2 :: Bool
testHelpers2 = ((\a b -> 2*a+3*b) >$< x1s >*< x2s) == [14, 19, 24]

testHelpers3 :: Bool
testHelpers3 = ((\a b c -> 2*a+3*b+5*c) >$< x1s >*< x2s >*< x3s) == [49, 59, 69]

testHelpers4 :: Bool
testHelpers4 = ((\a b c d -> 2*a+3*b+5*c-4*d) >$< x1s >*< x2s >*< x3s >*< x4s) == [9, 15, 21]

test :: Bool
test = testZipWith2 && testZipWith3 && testZipWith4
  && testAppZip2 && testAppZip3 && testAppZip4
  && testHelpers1 && testHelpers2 && testHelpers3 && testHelpers4

