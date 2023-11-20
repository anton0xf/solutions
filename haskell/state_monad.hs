{- https://stepik.org/lesson/8444/step/2?unit=1579
5.8 Монада State -}

newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State m) = State $ \s -> let (x, s1) = m s
                                   in (f x, s1)

instance Applicative (State s) where
  pure :: a -> State s a
  pure x = State (x,)
  
  (<*>) :: State s (a -> b) -> State s a -> State s b
  (State sf) <*> (State sx) = State $ \s ->
    let (f, s1) = sf s
        (x, s2) = sx s1 -- ???
    in (f x, s2)

instance Monad (State s) where
  (>>=) :: State s a -> (a -> State s b) -> State s b
  (State sx) >>= k = State $ \s ->
    let (x, s1) = sx s
        State sy = k x
    in sy s1
