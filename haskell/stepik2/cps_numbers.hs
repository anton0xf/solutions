{- https://stepik.org/lesson/30723/step/3?unit=11811
3.2.3. Монада Cont
CPS-преобразование часто применяют для создания предметно-ориентированных языков (DSL).
Реализуйте комбинаторы, которые позволят записывать числа вот в таком забавном формате: -}

test :: Bool
test = decode one as a number == 1
  && decode one hundred twenty three as a number == 123
  && decode one hundred twenty one as a number == 121
  && decode one hundred twenty as a number == 120
  && decode one hundred as a number == 100
  && decode three hundred as a number == 300
  && decode two thousand seventeen as a number == 2017

decode :: (Int -> r) -> r
decode c = c 0

noop :: Int -> (Int -> r) -> r
noop x c = c x

as :: Int -> (Int -> r) -> r
a :: Int -> (Int -> r) -> r
(as : a : _) = repeat noop

number :: r -> r
number = id

add :: Int -> Int -> (Int -> r) -> r
add x y c = c $ x + y

one :: Int -> (Int -> r) -> r
two :: Int -> (Int -> r) -> r
three :: Int -> (Int -> r) -> r
seventeen :: Int -> (Int -> r) -> r
twenty :: Int -> (Int -> r) -> r
[one, two, three, seventeen, twenty] = map add [1, 2, 3, 17, 20]

mult :: Int -> Int -> (Int -> r) -> r
mult x y c = c $ x * y

hundred :: Int -> (Int -> r) -> r
thousand :: Int -> (Int -> r) -> r
[hundred, thousand] = map mult [100, 1000]
