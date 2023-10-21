{-
4.2.9 https://stepik.org/lesson/4985/step/9

Целое число можно представить как список битов со знаком.

Реализуйте функции сложения и умножения для таких целых чисел,
считая, что младшие биты идут в начале списка, а старшие — в конце.
Можно считать, что на вход не будут подаваться числа с ведущими нулями. 
-}

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

data Bit = Zero | One deriving Eq
instance Show Bit where
  show Zero = "0"
  show One = "1"

data Sign = Minus | Plus
instance Show Sign where
  show Minus = "-"
  show Plus = "+"

data Z = Z Sign [Bit]
instance Show Z where
  show (Z s bs) = show s ++ concatMap show bs

bits = [Zero, One]

btoi :: Bit -> Integer
btoi Zero = 0
btoi One = 1

itob :: Integer -> Bit
itob 0 = Zero
itob 1 = One
itob n = error $ show n ++ " have to be 0 or 1"

ntoi :: [Bit] -> Integer
ntoi [] = 0
ntoi (b:bs) = btoi b + 2 * ntoi bs

iton :: Integer -> [Bit]
iton 0 = []
iton n | n > 0 = itob (n `mod` 2) : iton (n `div` 2)
       | otherwise = error $ show n ++ " should be non-negative"

ztoi :: Z -> Integer
ztoi (Z Plus bs) = ntoi bs
ztoi (Z Minus bs) = - ntoi bs

itoz :: Integer -> Z
itoz n | n >= 0 = Z Plus (iton n)
       | otherwise = Z Minus (iton (-n))

add' :: Z -> Z -> Z
add' x y = itoz $ ztoi x + ztoi y

-- ztoi $ itoz (-10) `add'` itoz 9
-- => -1

mul' :: Z -> Z -> Z
mul' x y = itoz $ ztoi x * ztoi y

-- direct approach

bitSum :: Bit -> Bit -> (Bit, Bit)
bitSum Zero Zero = (Zero, Zero)
bitSum One One = (One, One)
bitSum _ _ = (One, Zero)

{- mapM_ (\x -> print (x, (uncurry bitSum) x)) [(a, b) | a <- bits, b <- bits]
=>
((0,0),(0,0))
((0,1),(1,0))
((1,0),(1,0))
((1,1),(1,1))
-}

testBitSum :: Bool
testBitSum = all (\(args, value) -> uncurry bitSum args == value)
  [((Zero, Zero), (Zero, Zero)),
   ((Zero, One), (One, Zero)),
   ((One, Zero), (One, Zero)),
   ((One, One), (One, One))]

bitSum3 :: Bit -> Bit -> Bit -> (Bit, Bit)
bitSum3 a b c = case bitSum a b of
  (ab, ab') -> let (abc, abc') = bitSum ab c
                   (abc'', _) = bitSum ab' abc'
               in (abc, abc'')

{- mapM_ (\x -> print (x, (uncurry3 bitSum3) x)) [(a, b, c) | a <- bits, b <- bits, c <- bits]
=>
((0,0,0),(0,0))
((0,0,1),(1,0))
((0,1,0),(1,0))
((0,1,1),(1,1))
((1,0,0),(1,0))
((1,0,1),(1,1))
((1,1,0),(1,1))
((1,1,1),(1,1))
-}

testBitSum3 :: Bool
testBitSum3 = all (\(args, value) -> uncurry3 bitSum3 args == value)
  [((Zero, Zero, Zero), (Zero, Zero)),
   ((Zero, Zero, One), (One, Zero)),
   ((Zero, One, Zero), (One, Zero)),
   ((Zero, One, One), (One, One)),
   ((One, Zero, Zero), (One, Zero)),
   ((One, Zero, One), (One, One)),
   ((One, One, Zero), (One, One)),
   ((One, One, One), (One, One))]

-- add :: Z -> Z -> Z
-- add (Z _ []) y = y
-- add x (Z _ []) = x
-- add (Z sx (x:xs)) (Z sy (y:ys)) =
--   let rest = add (Z sx xs)
--   in undefined

