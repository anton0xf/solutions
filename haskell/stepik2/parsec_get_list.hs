{- https://stepik.org/lesson/42245/step/5?unit=20509
Реализуйте парсер getList, который разбирает строки из чисел, разделенных точкой с запятой,
и возвращает список строк, представляющих собой эти числа
-}

import Data.Function ((&))
import Text.Parsec

getList :: Parsec String u [String]
getList = many1 digit `sepBy` char ';'

left :: Show a => Either a b -> String
left = either show undefined

test :: Bool
test = parse getList "" "1;234;56" == Right ["1", "234", "56"]
  && (parse getList "" "1;234;56;" & left)
     == "(line 1, column 10):\nunexpected end of input\nexpecting digit"
  && (parse getList "" "1;;234;56" & left)
     == "(line 1, column 3):\nunexpected \";\"\nexpecting digit"
