{- https://stepik.org/lesson/31555/step/9?unit=11808
2.3.9. Законы и свойства класса Traversable -}

newtype Const c a = Const { getConst :: c }
  deriving (Eq, Show)

instance Functor (Const c) where
  fmap :: (a -> b) -> Const c a -> Const c b
  fmap _ (Const x) = Const x

instance Foldable (Const c) where
  foldr :: (a -> b -> b) -> b -> Const c a -> b
  foldr _ ini _ = ini

instance Traversable (Const c) where
  sequenceA :: Applicative f => Const c (f a) -> f (Const c a)
  sequenceA (Const c) = pure (Const c)

instance Monoid c => Applicative (Const c) where
  pure :: a -> Const c a
  pure _ = Const mempty

  (<*>) :: Const c (a -> b) -> Const c a -> Const c b
  (Const x) <*> (Const y) = Const (x <> y)
