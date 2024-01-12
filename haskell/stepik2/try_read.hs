{- https://stepik.org/lesson/30722/step/8?unit=11809
3.1.8. Монада Except -}

import Control.Monad.Trans.Except

{- Реализуйте функцию tryRead, получающую на вход строку и пытающуюся всю эту строку превратить
в значение заданного типа. Функция должна возвращать ошибку в одном из двух случаев:
если вход был пуст или если прочитать значение не удалось.

Информация об ошибке хранится в специальном типе данных: -}

data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

tryRead :: Read a => String -> Except ReadError a
tryRead "" = throwE EmptyInput
tryRead str = case filter (null . snd) $ reads str of
  [] -> throwE $ NoParse str
  [(x, "")] -> return x

test :: Bool
test = runExcept (tryRead "5" :: Except ReadError Int) == Right 5
  && runExcept (tryRead "5" :: Except ReadError Double) == Right 5.0
  && runExcept (tryRead "5zzz" :: Except ReadError Int) == Left (NoParse "5zzz")
  && runExcept (tryRead "(True, ())" :: Except ReadError (Bool, ())) == Right (True,())
  && runExcept (tryRead "" :: Except ReadError (Bool, ())) == Left EmptyInput
  && runExcept (tryRead "wrong" :: Except ReadError (Bool, ())) == Left (NoParse "wrong")

