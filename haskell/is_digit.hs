{- https://stepik.org/lesson/5746/step/6?unit=1256
4.4 Типы с параметрами step 6

Реализуйте функцию, которая ищет в строке первое вхождение символа,
который является цифрой, и возвращает Nothing, если в строке нет цифр.
-}

import Data.Char(isDigit)

findDigit :: [Char] -> Maybe Char
findDigit [] = Nothing
findDigit (c:cs) = if isDigit c
  then Just c
  else findDigit cs
