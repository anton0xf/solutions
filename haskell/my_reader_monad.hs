{- https://stepik.org/lesson/8441/step/2?unit=1576
5.6 Монада Reader
imppement it by myself
-}
newtype Env e v = Env {runEnv :: e -> v}

{- Laws
Identity: fmap id == id
Composition: fmap (f . g) == fmap f . fmap g
-}
instance Functor (Env e) where
  fmap :: (a -> b) -> Env e a -> Env e b
  fmap f (Env g) = Env $ f . g

{- Laws
Identity: pure id <*> v = v
Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
Homomorphism: pure f <*> pure x = pure (f x)
Interchange: u <*> pure y = pure ($ y) <*> u
-}
instance Applicative (Env e) where
  pure :: a -> Env e a
  pure x = Env $ const x

  (<*>) :: Env e (a -> b) -> Env e a -> Env e b
  (Env f) <*> (Env x) = Env (\e -> f e (x e))

{- Identity: pure id <*> v = v
(Env $ const id) <*> v
== Env (\e -> f e (x e))
-- f = const id, x = v
== Env (\e -> (const id) e (v e))
== Env (\e -> id (v e))
== Env (\e -> v e)
== v
-}
{- Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-}
{-Homomorphism: pure f <*> pure x = pure (f x)
-}
{- Interchange: u <*> pure y = pure ($ y) <*> u
-}

{- Laws
Left identity: return a >>= k = k a
Right identity: m >>= return = m
Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
-}
instance Monad (Env e) where
  (>>=) :: Env e a -> (a -> Env e b) -> Env e b
  (Env f) >>= k = Env (\e -> runEnv (k (f e)) e)
  
safeHead :: Env [a] (Maybe a)
safeHead = do
  b <- Env null
  if b then return Nothing
    else do fmap Just (Env head)

safeHead1 :: Env [a] (Maybe a)
safeHead1 = Env null >>= \b -> if b
  then return Nothing
  else fmap Just (Env head)

safeHead2 :: Env [a] (Maybe a)
safeHead2 = Env null >>= \b -> if b
  then Env (const Nothing)
  else Env (Just . head)

safeHead3 :: Env [a] (Maybe a)
safeHead3 = Env (\e -> runEnv
  ((\b -> if b
     then Env (const Nothing)
     else Env (Just . head))
   (null e)) e)

safeHead4 :: Env [a] (Maybe a)
safeHead4 = Env (\e ->
  if null e
  then Nothing
  else Just (head e))

checkSafeHead x y = all (\f -> runEnv f x == y)
  [safeHead, safeHead1, safeHead2, safeHead3, safeHead4]

testSafeHeads = checkSafeHead ([]::[Int]) Nothing
  && checkSafeHead [1,2,3] (Just 1)
