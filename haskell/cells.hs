{- https://stepik.org/lesson/5746/step/4?unit=1256
4.4 Типы с параметрами step 4

Плоскость разбита на квадратные ячейки. Стороны ячеек параллельны осям координат.
Координаты углов ячейки с координатой (0,0) имеют неотрицательные координаты.
Один из углов этой ячейки имеет координату (0,0). С ростом координат ячеек
увеличиваются координаты точек внутри этих ячеек.

Реализуйте функции getCenter, которая принимает координату ячейки
и возвращает координату ее центра, и функцию getCell,
которая принимает координату точки и возвращает номер ячейки
в которой находится данная точка. В качестве первого аргумента
обе эти функции принимают ширину ячейки.
-}

data Coord a = Coord a a deriving Show

getCenter :: Double -> Coord Int -> Coord Double
getCenter d (Coord i j) = Coord (center d i) (center d j)
  where center d i = d * (fromIntegral i + 0.5)

getCell :: Double -> Coord Double -> Coord Int
getCell d (Coord x y) = Coord (f d x) (f d y)
  where f d x = floor $ x / d
