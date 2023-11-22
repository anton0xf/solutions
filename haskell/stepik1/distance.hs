{- https://stepik.org/lesson/5746/step/3?unit=1256
4.4 Типы с параметрами step 3

Реализуйте функции distance, считающую расстояние между двумя точками
с вещественными координатами, и manhDistance, считающую манхэттенское
расстояние между двумя точками с целочисленными координатами.
-}

data Coord a = Coord a a

distance :: Coord Double -> Coord Double -> Double
distance (Coord x1 y1) (Coord x2 y2) = sqrt $ (x1 - x2)^2 + (y1 - y2)^2

manhDistance :: Coord Int -> Coord Int -> Int
manhDistance (Coord x1 y1) (Coord x2 y2) = abs (x1 - x2) + abs (y1 - y2)

test :: Bool
test = 5.0 == distance (Coord 0 0) (Coord 3 4)
  && 7 == manhDistance (Coord 0 0) (Coord 3 4)
