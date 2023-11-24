{- https://stepik.org/lesson/28880/step/8?unit=9912
1.1.8. Определение аппликативного функтора

Проверка законов функтора для списка.

Доказательство см. в ./functor_list.v
-}

data List a = Nil | Cons a (List a)
  deriving (Show, Eq)

instance Functor List where
  fmap _ Nil = Nil
  fmap f (Cons h tl) = Cons (f h) (fmap f tl)

-- Law 1: fmap id == id
testL1 :: Bool
testL1 = fmap id lst == lst where lst = [1..5]

{- https://stepik.org/lesson/28880/step/9?unit=9912 -}
-- Law 2: fmap (f . g) == fmap f . fmap g
testL2 :: Bool
testL2 = fmap (f . g) lst == (fmap f . fmap g) lst
  where lst = [1..5]
        f = (+2)
        g = (*3)

test :: Bool
test = testL1 && testL2
