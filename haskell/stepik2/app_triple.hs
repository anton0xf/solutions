{- https://stepik.org/lesson/28880/step/15?unit=9912
1.1.15. Определение аппликативного функтора

Следующий тип данных задает гомогенную тройку элементов, которую можно рассматривать
как трехмерный вектор: -}

data Triple a = Tr a a a deriving (Eq, Show)

{- Сделайте этот тип функтором и аппликативным функтором с естественной для векторов
семантикой покоординатного применения: -}

instance Functor Triple where
  fmap :: (a -> b) -> Triple a -> Triple b
  fmap f (Tr x y z) = Tr (f x) (f y) (f z)

instance Applicative Triple where
  pure :: a -> Triple a
  pure x = Tr x x x
  
  (<*>) :: Triple (a -> b) -> Triple a -> Triple b
  (Tr f g h) <*> (Tr x y z) = Tr (f x) (g y) (h z)

test = ((^2) <$> Tr 1 (-2) 3) == Tr 1 4 9
  && (Tr (^2) (+2) (*3) <*> Tr 2 3 4) == Tr 4 5 12
