{- https://stepik.org/lesson/30722/step/7?unit=11809
3.1.7. Монада Except -}

import Data.Foldable (msum)

{- В модуле Control.Monad.Trans.Except библиотеки transformers имеется реализация монады Except
с интерфейсом, идентичным представленному в видео-степах, но с более общими типами.
Мы изучим эти типы в следующих модулях, однако использовать монаду Except
из библиотеки transformers мы можем уже сейчас. -}

import Control.Monad.Trans.Except

{- Введём тип данных для представления ошибки обращения к списку по недопустимому индексу: -}

data ListIndexError = ErrIndexTooLarge Int | ErrNegativeIndex
  deriving (Eq, Show)

{- Реализуйте оператор (!!!) доступа к элементам массива по индексу,
отличающийся от стандартного (!!) поведением в исключительных ситуациях.
В этих ситуациях он должен выбрасывать подходящее исключение типа ListIndexError. -}

infixl 9 !!!
(!!!) :: [a] -> Int -> Except ListIndexError a
(!!!) xs n = if n < 0 then throwE ErrNegativeIndex
             else case drop n xs of
                    [] -> throwE (ErrIndexTooLarge n)
                    (x : _) -> return x

get3Test :: Bool
get3Test = runExcept ([1..100] !!! 5) == Right 6

(!!!!) :: [a] -> Int -> Either ListIndexError a
(!!!!) xs n = runExcept $ xs !!! n

get4Test :: Bool
get4Test = [1, 2, 3] !!!! 0 == Right 1
  && [1, 2, 3] !!!! 42 == Left (ErrIndexTooLarge 42)
  && [1, 2, 3] !!!! (-3) == Left ErrNegativeIndex

{- https://stepik.org/lesson/30722/step/13?unit=11809
3.1.13. Монада Except
Тип данных для представления ошибки обращения к списку по недопустимому индексу ListIndexError
не очень естественно делать представителем класса типов Monoid. Однако, если мы хотим обеспечить
накопление информации об ошибках, моноид необходим. К счастью, уже знакомая нам функция
withExcept :: (e -> e') -> Except e a -> Except e' a позволяет изменять тип ошибки
при вычислении в монаде Except.

Сделайте тип данных -}

newtype SimpleError = Simple { getSimple :: String }
  deriving (Eq, Show)

{- представителем необходимых классов типов и реализуйте преобразователь для типа данных ошибки -}

instance Semigroup SimpleError where
  (<>) :: SimpleError -> SimpleError -> SimpleError
  (Simple e1) <> (Simple e2) = Simple $ e1 ++ e2

instance Monoid SimpleError where
  mempty :: SimpleError
  mempty = Simple ""

lie2se :: ListIndexError -> SimpleError
lie2se ErrNegativeIndex = Simple "[negative index]"
lie2se (ErrIndexTooLarge n) = Simple $ "[index (" ++ show n ++ ") is too large]"

{- так, чтобы обеспечить следующее поведение -}

toSimple :: Except ListIndexError a -> Either SimpleError a
toSimple = runExcept . withExcept lie2se

xs :: [Integer]
xs = [1, 2, 3]

toSimpleTest :: Bool
toSimpleTest = toSimple (xs !!! 42) == Left (Simple "[index (42) is too large]")
  && toSimple (xs !!! (-2)) == Left (Simple "[negative index]")
  && toSimple (xs !!! 2) == Right 3

toSimpleFromList :: [Except ListIndexError a] -> Either SimpleError a
toSimpleFromList = runExcept . msum . map (withExcept lie2se)

toSimpleFromListTest :: Bool
toSimpleFromListTest = toSimpleFromList [xs !!! (-2), xs !!! 42]
      == Left (Simple "[negative index][index (42) is too large]")
  && toSimpleFromList [xs !!! (-2), xs !!! 2] == Right 3

test :: Bool
test = get3Test && get4Test && toSimpleTest && toSimpleFromListTest
