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

checkSafeHead :: Eq a => [a] -> Maybe a -> Bool
checkSafeHead x y = all (\f -> runEnv f x == y)
  [safeHead, safeHead1, safeHead2, safeHead3, safeHead4]

testSafeHeads :: Bool
testSafeHeads = checkSafeHead ([]::[Int]) Nothing
  && checkSafeHead [1,2,3] (Just 1)

{- https://stepik.org/lesson/8441/step/5?unit=1576 -}
ask :: Env e e
ask = Env id

testAsk :: Bool
testAsk = runEnv ask 42 == 42

type User = String
type Password = String
type UsersTable = [(User, Password)]

pwds :: UsersTable
pwds = [("Bill", "123"), ("Ann", "qwerty"), ("John", "2sRq8p")]

firstUser :: Env UsersTable User
firstUser = Env (fst . head)
-- do
--   e <- ask
--   return $ fst (head e)

testFirstUser :: Bool
testFirstUser = runEnv firstUser pwds == "Bill"

{- https://stepik.org/lesson/8441/step/6?unit=1576 -}
asks :: (e -> a) -> Env e a
asks = Env

firstUserPwd :: Env UsersTable Password
firstUserPwd = asks (snd . head)
-- do
--   pwd <- asks (snd . head)
--   reutrn pwd

testFirstUserPwd :: Bool
testFirstUserPwd = runEnv firstUserPwd pwds == "123"

usersCount :: Env UsersTable Int
usersCount = asks length

testUsersCount :: Bool
testUsersCount = runEnv usersCount pwds == 3

local :: (e -> e) -> Env e a -> Env e a
local f (Env g) = Env (g . f)

localEx :: Env UsersTable (Int, Int)
localEx = do
  c1 <- usersCount
  c2 <- local (("Mike", "1"):) usersCount
  return (c1, c2)

testLocalEx :: Bool
testLocalEx = runEnv localEx pwds == (3, 4)
  && runEnv localEx [] == (0, 1)

reader :: (e -> a) -> Env e a
reader = asks
-- reader f = do
--   e <- ask
--   return (f e)

{- https://stepik.org/lesson/8441/step/7?unit=1576 -}
local' :: (e1 -> e2) -> Env e2 a -> Env e1 a
local' f (Env g) = Env (g . f)

local'Ex :: Env UsersTable (Int, String)
local'Ex = do
  c1 <- usersCount
  c2 <- local' (("Mike", "1"),) $ asks (fst . fst)
  return (c1, c2)

testLocal'Ex :: Bool
testLocal'Ex = runEnv local'Ex pwds == (3, "Mike")

{- 5.6.9 https://stepik.org/lesson/8441/step/9?unit=1576
Реализуйте функцию, принимающую в качестве окружения UsersTable
и возвращающую список пользователей, использующих пароль "123456"
(в том же порядке, в котором они перечислены в базе).
-}
usersWithBadPasswords :: Env UsersTable [User]
usersWithBadPasswords = asks $ map fst . filter ((== "123456") . snd)
  -- \db -> [fst user | user <- db, snd user == "123456"]

testUsersWithBadPasswords :: Bool
testUsersWithBadPasswords = runEnv usersWithBadPasswords db == ["user", "root"]
  where db = [("user", "123456"), ("x", "hi"), ("root", "123456")]

test :: Bool
test = testSafeHeads && testAsk && testFirstUser && testFirstUserPwd
  && testUsersCount && testLocalEx && testLocal'Ex
  && testUsersWithBadPasswords
