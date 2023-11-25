{- https://stepik.org/lesson/30424/step/4?unit=11041
1.2.4. Представители класса типов Applicative - ZipList -}

newtype ZipList a = ZipList { getZipList :: [a] }
  deriving (Show, Eq)

instance Functor ZipList where
  fmap :: (a -> b) -> ZipList a -> ZipList b
  fmap f (ZipList xs) = ZipList $ map f xs

-- test ZipLlist
txs = ZipList [1..5]

-- Identity: fmap id == id
testFmapId :: Bool
testFmapId = fmap id txs == txs

-- Composition: fmap (f . g) == fmap f . fmap g
testFmapComp :: Bool
testFmapComp = fmap (f . g) txs == (fmap f . fmap g) txs
  where g = (*2)
        f = (+1)

instance Applicative ZipList where
  pure :: a -> ZipList a
  pure x = ZipList $ repeat x

  (<*>) :: ZipList (a -> b) -> ZipList a -> ZipList b
  (ZipList fs) <*> (ZipList xs) = ZipList $ zipWith ($) fs xs

-- Identity: pure id <*> v == v
testAppId :: Bool
testAppId = (pure id <*> txs) == txs

-- Composition: pure (.) <*> u <*> v <*> w == u <*> (v <*> w)
testAppComp :: Bool
testAppComp = (pure (.) <*> u <*> v <*> w) == (u <*> (v <*> w))
  where w = txs
        v = pure (+1)
        u = pure (*2)

-- Homomorphism: pure f <*> pure x == pure (f x)
testAppHom :: Bool
testAppHom = get (pure f <*> pure x) == get (pure $ f x)
  where x = 3
        f = (+ 1)
        get = (take 5) . getZipList

-- Interchange: u <*> pure y == pure ($ y) <*> u
testAppInt :: Bool
testAppInt = (u <*> pure y) == (pure ($ y) <*> u)
  where y = 3
        u = ZipList [(+1), (*2)]

test :: Bool
test = testFmapId && testFmapComp
  && testAppId && testAppComp && testAppHom && testAppInt
