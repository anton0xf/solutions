{- https://stepik.org/lesson/42245/step/7?unit=20509
1.3.7. Аппликативный парсер Parsec

Используя аппликативный интерфейс Parsec, реализуйте функцию ignoreBraces, которая принимает
три аргумента-парсера. Первый парсер разбирает текст, интерпретируемый как открывающая скобка,
второй — как закрывающая, а третий разбирает весь входной поток, расположенный между
этими скобками. Возвращаемый парсер возвращает результат работы третьего парсера,
скобки игнорируются.
-}
import Text.Parsec

ignoreBraces :: Parsec [Char] u a -> Parsec [Char] u b -> Parsec [Char] u c -> Parsec [Char] u c
ignoreBraces lbp rbp p = lbp *> p <* rbp

testP :: Parsec [Char] u [Char]
testP = ignoreBraces (string "[[") (string "]]") (many1 letter)

test :: Bool
test = parse testP "" "[[ABC]]DEF" == Right "ABC"
