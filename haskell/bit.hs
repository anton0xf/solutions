{-
4.2.9 https://stepik.org/lesson/4985/step/9

Целое число можно представить как список битов со знаком.

Реализуйте функции сложения и умножения для таких целых чисел,
считая, что младшие биты идут в начале списка, а старшие — в конце.
Можно считать, что на вход не будут подаваться числа с ведущими нулями. 
-}

data Bit = Zero | One
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

add :: Z -> Z -> Z
add x y = itoz $ ztoi x + ztoi y

-- ztoi $ itoz (-10) `add` itoz 9
-- => -1

mul :: Z -> Z -> Z
mul x y = itoz $ ztoi x * ztoi y
