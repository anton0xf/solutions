{- https://stepik.org/lesson/8437/step/3?unit=1572
5.2 Определение монады step 3
Введём следующий тип: -}
data Log a = Log [String] a deriving (Eq, Show)

{- Реализуйте вычисление с логированием, используя Log. Для начала определите функцию toLogger -}

toLogger :: (a -> b) -> String -> a -> Log b
toLogger f s x = Log [s] (f x)

{- которая превращает обычную функцию, в функцию с логированием: -}

add1Log = toLogger (+1) "added one"

test1 = add1Log 3 == Log ["added one"] 4

mult2Log = toLogger (* 2) "multiplied by 2"

test2 = mult2Log 3 == Log ["multiplied by 2"] 6

{- Далее, определите функцию execLoggers -}

execLoggers :: a -> (a -> Log b) -> (b -> Log c) -> Log c
execLoggers x f g = let Log ss1 x1 = f x
                        Log ss2 x2 = g x1
                    in Log (ss1 ++ ss2) x2

{- Которая принимает некоторый элемент и две функции с логированием.
execLoggers возвращает результат последовательного применения функций к элементу
и список сообщений, которые были выданы при применении каждой из функций: -}

test3 = execLoggers 3 add1Log mult2Log == Log ["added one", "multiplied by 2"] 8

test = test1 && test2 && test3
