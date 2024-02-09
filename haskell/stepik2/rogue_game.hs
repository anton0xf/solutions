{- https://stepik.org/lesson/38580/step/6?unit=20505
4.3.6. Трансформер ExceptT -}

import Data.Either
import Control.Monad.Trans
import Control.Monad.Trans.Except

{- Представьте, что друг принес вам игру. В этой игре герой ходит по полю. За один ход он может
переместиться на одну клетку вверх, вниз, влево и вправо (стоять на месте нельзя).
На поле его поджидают различные опасности, такие как пропасти (chasm) и ядовитые змеи (snake).
Если игрок наступает на клетку с пропастью или со змеёй, он умирает. -}

data Tile = Floor | Chasm | Snake
  deriving (Eq, Show)

data DeathReason = Fallen | Poisoned
  deriving (Eq, Show)

{- Карта задается функцией, отображающей координаты клетки в тип этой самой клетки: -}

type Point = (Integer, Integer)
type GameMap = Point -> Tile

{- Ваша задача состоит в том, чтобы реализовать функцию, принимающую карту, количество шагов
и начальную точку, а возвращающую список всех возможных исходов (с повторениями),
если игрок сделает заданное число шагов из заданной точки -}

-- throwE = ExceptT . return . Left
-- lift = ExceptT . fmap Right

moves :: GameMap -> Int -> Point -> [Either DeathReason Point]
moves _ 0 p = [Right p]
moves m n p = runExceptT $ do
  p' <- lift (steps p)
  stepOn m p'
  ExceptT $ moves m (n-1) p'

steps :: Point -> [Point]
steps (x, y) = [(x-1, y), (x, y-1), (x+1, y), (x, y+1)]

stepOn :: Monad m => GameMap -> Point -> ExceptT DeathReason m ()
stepOn m p = case m p of
  Floor -> return ()
  Chasm -> throwE Fallen
  Snake -> throwE Poisoned

{- Заодно реализуйте функцию, показывающую, сколькими способами игрок может умереть данным
способом, сделав заданное число шагов из заданной точки. -}

waysToDie :: DeathReason -> GameMap -> Int -> Point -> Int
waysToDie reason m n p = length $ filter (== reason) $ lefts $ moves m n p

{- Например, для такого поля: -}

map1 :: GameMap
map1 (2, 2) = Snake
map1 (4, 1) = Snake
map1 (x, y)
  | 0 < x && x < 5 && 0 < y && y < 5 = Floor
  | otherwise                        = Chasm

{-

 | 0 1 2 3 4 5
--------------
0| o o o o o o
1| o       s o
2| o   s     o
3| o         o
4| o         o
5| o o o o o o

ожидаются такие ответы: -}

waysToDieTest :: Bool
waysToDieTest = waysToDie Poisoned map1 1 (4,2) == 1  -- можно пойти к змее наверх
  &&  waysToDie Poisoned map1 2 (4,2) == 2  -- можно пойти к змее наверх или к змее влево
  && waysToDie Poisoned map1 3 (4,2) == 5
  -- за три шага к левой змее, по-прежнему можно дойти одним способом,
  -- а к правой — уже четырьмя (вверх, влево-вверх-вправо,
  --                            влево-вправо-вверх, вниз-вверх-вверх)
  && waysToDie Poisoned map1 4 (4,2) == 13

{- Гарантируется, что изначально игрок стоит на пустой клетке. -}

test :: Bool
test = waysToDieTest
