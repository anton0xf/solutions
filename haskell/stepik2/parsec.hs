{- https://stepik.org/lesson/42245/step/2?unit=20509
1.3.2. Аппликативный парсер Parsec -}
import Text.Parsec
import Data.Function ((&))

vowel :: Parsec [Char] u Char
vowel = oneOf "aeiou"

testDigit :: Bool
testDigit = parse digit "" "1a" == Right '1'
  && (parse digit "tst" "a" & either show undefined)
     == "\"tst\" (line 1, column 1):\nunexpected \"a\"\nexpecting digit"

