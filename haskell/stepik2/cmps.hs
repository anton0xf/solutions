{- https://stepik.org/lesson/30426/step/2?unit=11043
1.5.2. Композиция на уровне типов -}
{-# LANGUAGE TypeOperators #-}

infixr 9 |.|
newtype (|.|) f g a = Cmps { getCmps :: f (g a) }
  deriving (Show, Eq)

