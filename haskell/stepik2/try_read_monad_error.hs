{- https://stepik.org/lesson/45331/step/2?unit=23645
4.5.2. Задачи на трансформеры -}

import Data.Monoid
import Text.Read
import Control.Monad.Writer
import Control.Monad.Except

{- Функция tryRead обладает единственным эффектом: в случае ошибки она должна прерывать
вычисление. Это значит, что её можно использовать в любой монаде, предоставляющей возможность
завершать вычисление с ошибкой, но сейчас это не так, поскольку её тип это делать не позволяет: -}

data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

-- tryRead :: (Read a, Monad m) => String -> ExceptT ReadError m a

{- Измените её так, чтобы она работала в любой монаде, позволяющей сообщать об исключительных
ситуациях типа ReadError. Для этого к трансформеру ExceptT в библиотеке mtl прилагается класс
типов MonadError (обратите внимание на название класса — это так сделали специально, чтобы всех
запутать), находящийся в модуле Control.Monad.Except. -}

tryRead :: (Read a, MonadError ReadError m) => String -> m a
tryRead "" = throwError EmptyInput
tryRead str = case readMaybe str of
  Nothing -> throwError $ NoParse str
  Just x -> return x

type ReadExcept = Except ReadError

tryReadTest :: Bool
tryReadTest = runExcept (tryRead "5" :: ReadExcept Int) == Right 5
  && runExcept (tryRead "5" :: ReadExcept Double) == Right 5.0
  && runExcept (tryRead "5zzz" :: ReadExcept Int) == Left (NoParse "5zzz")
  && runExcept (tryRead "(True, ())" :: ReadExcept (Bool, ())) == Right (True,())
  && runExcept (tryRead "" :: ReadExcept (Bool, ())) == Left EmptyInput
  && runExcept (tryRead "wrong" :: ReadExcept (Bool, ())) == Left (NoParse "wrong")

{- https://stepik.org/lesson/45331/step/3?unit=23645
4.5.3. Задачи на трансформеры

В очередной раз у вас есть дерево строковых представлений чисел и функция tryRead -}

data Tree a = Leaf a | Fork (Tree a) a (Tree a)
  deriving (Show, Eq)

{- Просуммируйте числа в дереве, а если хотя бы одно прочитать не удалось, верните ошибку:  -}

treeSumTest :: Bool
treeSumTest = treeSum (Fork (Fork (Leaf "1") "2" (Leaf "oops")) "15" (Leaf "16"))
      == Left (NoParse "oops")
  && treeSum (Fork (Fork (Leaf "1") "2" (Leaf "0")) "15" (Leaf "16")) == Right 34

treeSum :: Tree String -> Either ReadError Integer
treeSum = toEither . runWriter . runExceptT . iter
  where
    readAndTell :: String -> ExceptT ReadError (Writer (Sum Integer)) ()
    readAndTell s = tryRead s >>= tell . Sum

    iter :: Tree String -> ExceptT ReadError (Writer (Sum Integer)) ()
    iter (Leaf s) = readAndTell s
    iter (Fork t1 s t2) = do
      iter t1
      n <- tryRead s
      tell $ Sum n
      iter t2

    toEither :: (Either ReadError (), Sum Integer) -> Either ReadError Integer
    toEither (Left e, _) = Left e
    toEither (_, n) = Right $ getSum n

test :: Bool
test = tryReadTest && treeSumTest
