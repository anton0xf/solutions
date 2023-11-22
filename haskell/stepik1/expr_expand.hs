{- https://stepik.org/lesson/7009/step/8?unit=1472
4.5 Рекурсивные типы данных step 8
Исправьте определение функции expand так, чтобы она,
используя дистрибутивность (а также, возможно, ассоциативность и коммутативность),
всегда возвращала значение, эквивалентное данному
и являющееся суммой произведений числовых значений. Например,

GHCi> expand $ (Val 1 :+: Val 2 :+: Val 3) :*: (Val 4 :+: Val 5)
Val 1 :*: Val 4 :+: (Val 1 :*: Val 5
  :+: (Val 2 :*: Val 4 :+: (Val 2 :*: Val 5 :+: (Val 3 :*: Val 4 :+: Val 3 :*: Val 5))))

Примечание. Скобки в ответе могут быть расставлены по-другому или вообще отсутствовать, поскольку сложение ассоциативно. Слагаемые могут идти в другом порядке, поскольку сложение коммутативно.
-}

infixl 6 :+:
infixl 7 :*:
data Expr = Val Int | Expr :+: Expr | Expr :*: Expr
    deriving (Show, Eq)

expand :: Expr -> Expr
expand (e1 :+: e2) = expand e1 :+: expand e2
expand (e1 :*: e2) = f $ expand e1 :*: expand e2 where
  f ((e1 :+: e2) :*: e) = f (e1 :*: e) :+: f (e2 :*: e)
  f (e :*: (e1 :+: e2)) = f (e :*: e1) :+: f (e :*: e2)
  f e = e
expand e = e

{- examples:
Val 1 :*: (Val 2 :+: Val 3) :*: Val 4
(Val 1 :+: Val 2 :+: Val 3) :*: (Val 4 :+: Val 5)
(Val 1 :+: Val 2 :+: Val 3) :*: (Val 4 :+: Val 5) :*: (Val 6 :+: Val 7)
-}
