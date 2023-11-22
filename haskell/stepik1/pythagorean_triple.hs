{- https://stepik.org/lesson/8439/step/8?unit=1574
5.4 Список и Maybe как монады step 8

Используя монаду списка и do-нотацию, реализуйте функцию

которая принимает на вход некоторое число x и возвращает список троек (a,b,c),
таких что

a^2 + b^2 = c^2, a>0, b>0, c>0, c≤x, a<b

Число x может быть ≤0, на таком входе должен возвращаться пустой список.
-}

pythagoreanTriple :: Int -> [(Int, Int, Int)]
pythagoreanTriple x = do
  True <- [x > 0]
  a <- [1..x]
  b <- [(a + 1)..x]
  c <- [1..x]
  True <- [a^2 + b^2 == c^2]
  return (a, b, c)

test = pythagoreanTriple 5 == [(3,4,5)]
  && null (pythagoreanTriple 0)
  && pythagoreanTriple 10 == [(3,4,5), (6,8,10)]



