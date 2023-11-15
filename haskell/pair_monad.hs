data Pair a b = Pair a b

instance Monoid e => Functor (Pair e) where
  fmap :: Monoid e => (a -> b) -> Pair e a -> Pair e b
  fmap f (Pair e x) = Pair e (f x)

instance Monoid e => Applicative (Pair e) where
  pure :: Monoid e => a -> Pair e a
  pure = Pair mempty
  
  (<*>) :: Monoid e => Pair e (a -> b) -> Pair e a -> Pair e b
  (Pair e0 f) <*> (Pair e1 x) = Pair (mappend e0 e1) (f x)

instance Monoid e => Monad (Pair e) where
  (>>=) :: Monoid e => Pair e a -> (a -> Pair e b) -> Pair e b
  (Pair e0 x) >>= k = let (Pair e1 y) = k x in Pair (mappend e0 e1) y


{-
return x >>= k
== (Pair mempty x) >>= k
== let (Pair e1 y) = k x
   in Pair (mappend mempty e1) y
== let (Pair e1 y) = k x
   in Pair e1 y
== k x

m >>= return
== (Pair e x) >>= (Pair mempty)
== let (Pair e1 y) = (Pair mempty) x
   in Pair (mappend e e1) y
== let e1 = mempty
       y = x
   in Pair (mappend e e1) y
== Pair (mappend e mempty) x
== Pair e x == m

(m >>= k) >>= h  ==  m >>= \x -> k x >>= h
(Pair e x >>= k) >>= h  ==  Pair e x >>= \x -> k x >>= h
(let (Pair e1 y) = k x in Pair (mappend e e1) y) >>= h
  == Pair e x >>= \z -> k z >>= h
  == let (Pair e1 y) = (\z -> k z >>= h) x in Pair (mappend e e1) y
  == let (Pair e1 y) = (k x >>= h) in Pair (mappend e e1) y
  == let (Pair e1 w) = (k x >>= h) in Pair (mappend e e1) w
     > k x >>= h
     > == let (Pair e1 y) = k x
              (Pair e2 z) = h y
          in Pair (mappend e1 e2) z
  == let (Pair e1 w)
       = let (Pair e1 y) = k x
             (Pair e2 z) = h y
         in Pair (mappend e1 e2) z
     in Pair (mappend e e1) w
  == let (Pair e3 w)
       = let (Pair e1 y) = k x
             (Pair e2 z) = h y
         in Pair (mappend e1 e2) z
     in Pair (mappend e e3) w
  == let (Pair e1 y) = k x
         (Pair e2 z) = h y
         (Pair e3 w) = Pair (mappend e1 e2) z
     in Pair (mappend e e3) w
  == let (Pair e1 y) = k x
         (Pair e2 z) = h y
         e3 = mappend e1 e2
         w = z
     in Pair (mappend e e3) w
  == let (Pair e1 y) = k x
         (Pair e2 z) = h y
     in Pair (mappend e (mappend e1 e2)) z

(let (Pair e1 y) = k x in Pair (mappend e e1) y) >>= h
  == ( let (Pair e1 y) = k x
       in Pair (mappend e e1) y
     ) >>= h
  == let (Pair e1 y) = k x
     in (Pair (mappend e e1) y) >>= h
  -- (Pair e0 x) >>= k = let (Pair e1 y) = k x in Pair (mappend e0 e1) y
  -- e1 -> e2
  -- (Pair e0 x) >>= k = let (Pair e2 y) = k x in Pair (mappend e0 e2) y
  -- e0 -> (mappend e e1)
  -- k -> h
  -- x -> y -> z 

  -- (Pair (mappend e e1) y) >>= h
     == let (Pair e2 z) = h y
        in Pair (mappend (mappend e e1) e2) z

  == let (Pair e1 y) = k x
     in let (Pair e2 z) = h y
        in Pair (mappend (mappend e e1) e2) z
  == let (Pair e1 y) = k x
         (Pair e2 z) = h y
      in Pair (mappend (mappend e e1) e2) z
-}
