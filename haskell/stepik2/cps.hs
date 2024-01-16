{- https://stepik.org/lesson/30723/step/2?unit=11811
3.2.2. Монада Cont -}

square :: Int -> (Int -> r) -> r
square x c = c $ x^2

add :: Int -> Int -> (Int -> r) -> r
add x y c = c $ x + y

combTest :: Bool
combTest = add 1 2 square id == 9
  && square 2 (add 3) (add 5) id == 12

{- https://stepik.org/lesson/30723/step/4?unit=11811
3.2.4. Монада Cont -}
sumSquares :: Int -> Int -> (Int -> r) -> r
sumSquares x y c = square x $ \x2 ->
  square y $ \y2 ->
  add x2 y2 c

sumSquaresTest :: Bool
sumSquaresTest = sumSquares 3 4 id == 25

test :: Bool
test = combTest && sumSquaresTest
