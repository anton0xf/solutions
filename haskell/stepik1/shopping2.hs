{- https://stepik.org/lesson/8442/step/7?unit=1577
5.7 Монада Writer step 7

Измените определение типа Shopping и доработайте функцию purchase из предыдущего задания
таким образом, чтобы можно было реализовать функцию items, возвращающую список купленных товаров
(в том же порядке, в котором они были перечислены при покупке):

Реализуйте функцию items и исправьте функцию total, чтобы она работала как и прежде.
-}

import Control.Monad.Writer

type Shopping = Writer ([String], Sum Integer) ()

purchase :: String -> Integer -> Shopping
purchase item cost = tell ([item], Sum cost)

total :: Shopping -> Integer
total = getSum . snd . execWriter

items :: Shopping -> [String]
items = fst . execWriter

shopping1 :: Shopping
shopping1 = do
  purchase "Jeans"   19200
  purchase "Water"     180
  purchase "Lettuce"   328

testTotal = total shopping1 == 19708
testItems = items shopping1 == ["Jeans","Water","Lettuce"]

test = testTotal && testItems
