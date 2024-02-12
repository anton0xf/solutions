{- https://stepik.org/lesson/38580/step/12?unit=20505
4.3.12. Трансформер ExceptT -}

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Except

{- Вспомним функцию tryRead: -}

data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

{-
tryRead :: Read a => String -> Except ReadError a
 
Измените её так, чтобы она работала в трансформере ExceptT.
-}

tryRead :: (Monad m, Read a) => String -> ExceptT ReadError m a
tryRead "" = throwE EmptyInput
tryRead str = case filter (null . snd) $ reads str of
  [] -> throwE $ NoParse str
  [(x, "")] -> return x

type ReadExcept = Except ReadError

tryReadTest :: Bool
tryReadTest = runExcept (tryRead "5" :: ReadExcept Int) == Right 5
  && runExcept (tryRead "5" :: ReadExcept Double) == Right 5.0
  && runExcept (tryRead "5zzz" :: ReadExcept Int) == Left (NoParse "5zzz")
  && runExcept (tryRead "(True, ())" :: ReadExcept (Bool, ())) == Right (True,())
  && runExcept (tryRead "" :: ReadExcept (Bool, ())) == Left EmptyInput
  && runExcept (tryRead "wrong" :: ReadExcept (Bool, ())) == Left (NoParse "wrong")

test :: Bool
test = tryReadTest
