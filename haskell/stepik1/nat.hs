{- https://stepik.org/lesson/7009/step/4?unit=1472
4.5 Рекурсивные типы данных step 4

Рассмотрим еще один пример рекурсивного типа данных:

data Nat = Zero | Suc Nat

Элементы этого типа имеют следующий вид: Zero, Suc Zero, Suc (Suc Zero),
Suc (Suc (Suc Zero)), и так далее. Таким образом мы можем считать,
что элементы этого типа - это натуральные числа в унарной системе счисления.

Мы можем написать функцию, которая преобразует Nat в Integer следующим образом:

fromNat :: Nat -> Integer
fromNat Zero = 0
fromNat (Suc n) = fromNat n + 1

Реализуйте функции сложения и умножения этих чисел, а также функцию, вычисляющую факториал.
-}

data Nat = Zero | Suc Nat
  deriving Show

fromNat :: Nat -> Integer
fromNat Zero = 0
fromNat (Suc n) = fromNat n + 1

toNat :: Integer -> Nat
toNat 0 = Zero
toNat n = if n > 0 then Suc $ toNat (n-1)
  else error (show n ++ " should be non-negative")

add :: Nat -> Nat -> Nat
add Zero n = n
add (Suc m) n = Suc $ add m n

mul :: Nat -> Nat -> Nat
mul Zero _ = Zero
mul (Suc m) n = n `add` mul m n

fac :: Nat -> Nat
fac Zero = Suc Zero
fac n@(Suc n') = n `mul` fac n'

test :: Bool
test = f == 24
  where f = fromNat . fac . toNat $ 4
