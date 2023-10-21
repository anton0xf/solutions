{- https://stepik.org/lesson/5431/step/8?unit=1132


4.3 Синтаксис записей step 8

Определить функцию abbrFirstName, которая сокращает имя до первой буквы с точкой,
то есть, если имя было "Ivan", то после применения этой функции оно превратится в "I.".
Однако, если имя было короче двух символов, то оно не меняется.

-}

data Person = Person { firstName :: String, lastName :: String, age :: Int }
  deriving (Show, Eq)

abbrFirstName :: Person -> Person
abbrFirstName p@(Person {firstName = fn})
  | length fn <= 2 = p
  | otherwise      = p {firstName = head fn : "."}


testAbbrFirstName :: Person -> Person -> Bool
testAbbrFirstName input expected
  = abbrFirstName input == expected

test :: Bool
test = t1 && t2
  where
    p1 = Person { firstName = "Fn", lastName = "Ln", age = 20 }
    t1 = testAbbrFirstName p1 p1
    
    p2 = p1 { firstName = "Fname" }
    p2' = p1 { firstName = "F." }
    t2 = testAbbrFirstName p2 p2'
