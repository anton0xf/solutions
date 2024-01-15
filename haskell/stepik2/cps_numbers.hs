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
as = noop

a :: Int -> (Int -> r) -> r
a = noop

number :: r -> r
number = id

num :: Int -> Int -> (Int -> r) -> r
num x y c = c $ x + y

one :: Int -> (Int -> r) -> r
one = num 1

two :: Int -> (Int -> r) -> r
two = num 2

three :: Int -> (Int -> r) -> r
three = num 3

seventeen :: Int -> (Int -> r) -> r
seventeen = num 17

twenty :: Int -> (Int -> r) -> r
twenty = num 20

hundred :: Int -> (Int -> r) -> r
hundred x c = c $ x * 100

thousand :: Int -> (Int -> r) -> r
thousand x c = c $ x * 1000
