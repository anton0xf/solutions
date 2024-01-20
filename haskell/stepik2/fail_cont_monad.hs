{- https://stepik.org/lesson/30723/step/10?unit=11811
3.2.10. Монада Cont -}

import Data.Bifunctor
import Control.Monad.Trans.Except

{- Вычисление в монаде Cont передает результат своей работы в функцию-продолжение.
А что, если наши вычисления могут завершиться с ошибкой? В этом случае мы могли бы явно возвращать
значение типа Either и каждый раз обрабатывать два возможных исхода, что не слишком удобно.
Более разумный способ решения этой проблемы предоставляют трансформеры монад, но с ними мы
познакомимся немного позже.

Определите тип данных FailCont для вычислений, которые получают два продолжения и вызывают одно
из них в случае успеха, а другое — при неудаче. Сделайте его представителем класса типов Monad
и реализуйте вспомогательные функции toFailCont и evalFailCont, используемые в следующем коде: -}

add :: Int -> Int -> FailCont r e Int
add x y = FailCont $ \ok _ -> ok $ x + y

addInts :: String -> String -> FailCont r ReadError Int
addInts s1 s2 = do
  i1 <- toFailCont $ tryRead s1
  i2 <- toFailCont $ tryRead s2
  return $ i1 + i2

{- (Здесь используется функция tryRead из предыдущего урока; определять её заново не надо.) -}

addIntsTest :: Bool
addIntsTest = evalFailCont (addInts "15" "12") == Right 27
  && runFailCont (addInts "15" "") show (("Oops: " ++) . show) == "Oops: EmptyInput"

-- other definitions
data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

tryRead :: Read a => String -> Except ReadError a
tryRead "" = throwE EmptyInput
tryRead str = case filter (null . snd) $ reads str of
  [] -> throwE $ NoParse str
  [(x, "")] -> return x

-- solution
newtype FailCont r e a = FailCont { runFailCont :: (a -> r) -> (e -> r) -> r}

toFailCont :: Except e a -> FailCont r e a
toFailCont mx = FailCont (\vc ec -> either ec vc $ runExcept mx)

evalFailCont :: FailCont (Either e a) e a -> Either e a
evalFailCont (FailCont cx) = cx Right Left

instance Functor (FailCont r e) where
  fmap :: (a -> b) -> FailCont r e a -> FailCont r e b
  fmap f (FailCont cx) = FailCont $ \vc ec -> cx (vc . f) ec

instance Applicative (FailCont r e) where
  pure :: a -> FailCont r e a
  pure x = FailCont $ \vc _ -> vc x

  (<*>) :: FailCont r e (a -> b) -> FailCont r e a -> FailCont r e b
  (FailCont cf) <*> (FailCont cx) = FailCont $ \vc ec -> cf (\f -> cx (vc . f) ec) ec

instance Monad (FailCont r e) where
  (>>=) :: FailCont r e a -> (a -> FailCont r e b) -> FailCont r e b
  (FailCont cx) >>= k = FailCont $ \vc ec -> cx (\x -> runFailCont (k x) vc ec) ec

{- https://stepik.org/lesson/30723/step/13?unit=11811
3.2.13. Монада Cont
Реализуйте функцию callCFC для монады FailCont по аналогии с callCC. -}

callCFC :: ((a -> FailCont r e b) -> FailCont r e a) -> FailCont r e a
callCFC f = FailCont $ \ok err -> runFailCont (f $ \x -> FailCont $ \_ _ -> ok x) ok err

-- all tests
test :: Bool
test = addIntsTest
