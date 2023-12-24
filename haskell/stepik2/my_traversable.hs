{- https://stepik.org/lesson/30428/step/8?unit=11045
2.2.8. Класс типов Traversable -}

class (Functor t, Foldable t) => Trav t where
  seqA :: Applicative f => t (f a) -> f (t a)
  seqA = trav id

  trav :: Applicative f => (a -> f b) -> t a -> f (t b)
  trav g = seqA . fmap g

{- https://stepik.org/lesson/30428/step/9?unit=11045 -}

instance Trav Maybe where
  seqA :: Applicative f => Maybe (f a) -> f (Maybe a)
  seqA Nothing = pure Nothing
  seqA (Just fx) = Just <$> fx

travMaybeTest :: Bool
travMaybeTest = trav g (Just 5) == [Just 5, Just 7, Just 25]
                && trav g Nothing == [Nothing]
                && seqA (Just ("Abc", 3)) == ("Abc", Just 3)
  where g x = [x, x+2, x^2]

instance Trav (Either e) where
  seqA :: Applicative f => Either e (f a) -> f (Either e a)
  seqA (Left e) = pure $ Left e
  seqA (Right fx) = Right <$> fx

{- https://stepik.org/lesson/30428/step/10?unit=11045 -}
instance Trav ((,) e) where
  seqA :: Applicative f => (e, f a) -> f (e, a)
  seqA (e, fx) = (e,) <$> fx

instance Trav [] where
  seqA :: Applicative f => [f a] -> f [a]
  seqA [] = pure []
  seqA (fx : fxs) = (:) <$> fx <*> seqA fxs

travListTest :: Bool
travListTest = null (seqA [Just 1, Nothing])
  && seqA [Just 1, Just 2] == Just [1, 2]

test :: Bool
test = travMaybeTest && travListTest
