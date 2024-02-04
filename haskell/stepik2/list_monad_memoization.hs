{- https://stepik.org/lesson/38578/step/6?discussion=8960923&reply=8975426&unit=20503
from discussion at 4.1.6. Трансформер WriterT -}

{-
Дан список положительных целых чисел (xs :: [Int]).
Начинаем с первого элемента x = head xs.
Далее можно прыгнуть на j = 1..x элементов вперёд и продолжить с этого места.
Т.е. рекусивно продолжем для списка xs' = drop j xs.
Заканчиваем, когда список закончился.
Для каждого такого пути считаем сумму значений x посещённых элементов списка.
Задача получить распределение этих сумм в зависисимости от выбора j,
т.е. сколько каких значений сумм получится, если пройти по всем возможным путям
-}

import Data.Map (Map)
import Data.Map qualified as Map

-- list -> Map (sum -> count)
jumps :: [Int] -> Map Int Int
jumps [] = Map.singleton 0 1
jumps (x : xs) = Map.fromListWith (+) $ do
     j <- [0 .. (x-1)]
     (sum, count) <- Map.toList $ jumps $ drop j xs
     return (sum + x, count)

