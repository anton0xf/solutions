{- https://stepik.org/lesson/8444/step/2?unit=1579
5.8 Монада State -}

newtype State s a = State { runState :: s -> (a, s) }

stateA :: State Integer String
stateA = State $ \s -> ("A", s + 1)

stateEq :: (Eq s, Eq a) => s -> State s a -> State s a -> Bool
stateEq s (State m1) (State m2) = m1 s == m2 s

checkStateEq :: (Eq s, Eq a) => State s a -> State s a -> [s] -> Bool
checkStateEq (State m1) (State m2) = all (\s -> m1 s == m2 s)

checkEqIntStrSt :: State Integer String -> State Integer String -> Bool
checkEqIntStrSt m1 m2 = checkStateEq m1 m2 [0..5]

{- Laws
Identity: fmap id == id
Composition: fmap (f . g) == fmap f . fmap g
-}
instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State m) = State $ \s -> let (x, s1) = m s
                                   in (f x, s1)

testFmapId :: Bool
testFmapId = checkEqIntStrSt (fmap id stateA) stateA

testFmapComp :: Bool
testFmapComp = checkEqIntStrSt (fmap (f . g) stateA) (fmap f . fmap g $ stateA)
  where f = (++ "B")
        g = (++ "C")

{- Laws
Identity: pure id <*> v = v
Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
Homomorphism: pure f <*> pure x = pure (f x)
Interchange: u <*> pure y = pure ($ y) <*> u
-}
instance Applicative (State s) where
  pure :: a -> State s a
  pure x = State (x,)
  
  (<*>) :: State s (a -> b) -> State s a -> State s b
  (State sf) <*> (State sx) = State $ \s ->
    let (f, s1) = sf s
        (x, s2) = sx s1
    in (f x, s2)

testAppId :: Bool
testAppId = checkEqIntStrSt (pure id <*> stateA) stateA

testAppComp :: Bool
testAppComp = checkEqIntStrSt (pure (.) <*> u <*> v <*> w) (u <*> (v <*> w))
  where u = State $ \s -> ((++ "C"), s^2)
        v = State $ \s -> ((++ "B"), s * 3)
        w = stateA

testAppHom :: Bool
testAppHom = checkEqIntStrSt (pure f <*> pure x) (pure $ f x)
  where x = "ab"
        f = (++ "c")

testAppInt :: Bool
testAppInt = checkEqIntStrSt (u <*> pure y) (pure ($ y) <*> u)
  where y = "ab"
        u = State $ \s -> ((++ "c"), s * 2)

{- Laws
Left identity: return a >>= k = k a
Right identity: m >>= return = m
Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
-}
instance Monad (State s) where
  (>>=) :: State s a -> (a -> State s b) -> State s b
  (State sx) >>= k = State $ \s ->
    let (x, s1) = sx s
        State sy = k x
    in sy s1

testBindLId :: Bool
testBindLId = checkEqIntStrSt (return a >>= k) (k a)
  where a = "ab"
        k x = State $ \s -> ("c" ++ x, s + 3)

testBindRId :: Bool
testBindRId = checkEqIntStrSt (stateA >>= return) stateA

testBindAssoc :: Bool
testBindAssoc = checkEqIntStrSt ((m >>= k) >>= h) (m >>= (\x -> k x >>= h))
  where m = stateA
        k x = State $ \s -> ("B" ++ x, s * 2)
        h x = State $ \s -> (x ++ "C", s^2)

execState :: State s a -> s -> s
execState m s = snd $ runState m s

testExecState :: Bool
testExecState = execState stateA 0 == 1

evalState :: State s a -> s -> a
evalState m s = fst $ runState m s

testEvalState :: Bool
testEvalState = evalState stateA 0 == "A"

test :: Bool
test = testFmapId && testFmapComp
  && testAppId && testAppComp && testAppHom && testAppInt
  && testBindLId && testBindRId && testBindAssoc
  && testExecState && testEvalState
