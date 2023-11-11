{- https://stepik.org/lesson/8439/step/6?unit=1574
5.4 Список и Maybe как монады step 6

Пусть имеется тип данных, который описывает конфигурацию шахматной доски:

data Board = ...

Кроме того, пусть задана функция

nextPositions :: Board -> [Board]

которая получает на вход некоторую конфигурацию доски и возвращает
все возможные конфигурации, которые могут получиться,
если какая-либо фигура сделает один ход. Напишите функцию:

nextPositionsN :: Board -> Int -> (Board -> Bool) -> [Board]

которая принимает конфигурацию доски, число ходов n, предикат
и возвращает все возможные конфигурации досок, которые могут получиться,
если фигуры сделают n ходов и которые удовлетворяют заданному предикату.
При n < 0 функция возвращает пустой список.
-}

--Тип Board и функция nextPositions заданы, реализовывать их не нужно
newtype Board = Board {fromBoard :: Integer} deriving Show

nextPositions :: Board -> [Board]
nextPositions (Board n) = [Board (n-1), Board (n+1)]

nextPositionsN :: Board -> Int -> (Board -> Bool) -> [Board]
nextPositionsN b 0 pred = [b | pred b]
nextPositionsN b n pred = if n < 0 then [] else do
  b1 <- nextPositions b
  nextPositionsN b1 (n-1) pred

test1 = all (uncurry check)
   [(0, [0]),
    (1, [-1, 1]),
    (2, [-2, 0, 0, 2]),
    (3, [-3, -1, -1, 1, -1, 1, 1, 3])]
  where check n exp = exp == map fromBoard
          (nextPositionsN (Board 0) n (const True))

test2 = [1,1,1,3] == map fromBoard
  (nextPositionsN (Board 0) 3 ((>0) . fromBoard))

test = test1 && test2
