{- https://stepik.org/lesson/30722/step/7?unit=11809
3.1.7. Монада Except
В модуле Control.Monad.Trans.Except библиотеки transformers имеется реализация монады Except
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

test :: Bool
test = get3Test && get4Test
