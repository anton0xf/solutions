module ListState where

import Control.Monad.State

newtype ListState st a = LST { getLST :: [State st a] }

-- run/eval/exec/trace
runLST :: ListState st a -> st -> ([a], st)
runLST (LST []) st = ([], st)
runLST (LST (mx : mxs)) st = let
      (x, st1) = runState mx st
      (xs, stn) = runLST (LST mxs) st1
  in (x : xs, stn)

evalLST :: ListState st a -> st -> [a]
evalLST m st = fst (runLST m st)

execLST :: ListState st a -> st -> st
execLST m st = snd (runLST m st)

traceLST :: ListState st a -> st -> [(a, st)]
traceLST (LST []) st = []
traceLST (LST (mx : mxs)) st = let
      (x, st1) = runState mx st
  in (x, st1) : traceLST (LST mxs) st1

-- creation utils
-- list with state function
listWithStf :: [a] -> (st -> st) -> ListState st a
listWithStf xs f = LST [state $ \st -> (x, f st) | x <- xs]

-- usage example
doubleWithSum :: [Int] -> ListState Int Int
doubleWithSum xs = LST [state $ \st -> (x * 2, st + x) | x <- xs]

doubleWithSumTest :: Bool
doubleWithSumTest = runLST (doubleWithSum [0..3]) 1 == ([0, 2, 4, 6], 7)

-- test util
mA :: ListState Int Char
mA = listWithStf "Cde" (+1)
  -- LST [state $ \st -> (ch, st + 1) | ch <- "Cde"]

mATest :: Bool
mATest = runLST mA 0 == ("Cde", 3)

lstEq :: (Eq st, Eq a) => ListState st a -> ListState st a -> st -> Bool
lstEq (LST m1) (LST m2) st = map (`runState` st) m1 == map (`runState` st) m2

lstEqList :: (Eq st, Eq a) => ListState st a -> ListState st a -> [st] -> Bool
lstEqList m1 m2 = all $ lstEq m1 m2

check :: ListState Int Char -> ListState Int Char -> Bool
check m1 m2 = lstEqList m1 m2 [0..5]

{- Laws
Identity: fmap id == id
Composition: fmap (f . g) == fmap f . fmap g
-}
instance Functor (ListState st) where
  fmap :: (a -> b) -> ListState st a -> ListState st b
  fmap f (LST ms) = LST [f <$> m | m <- ms]
  -- fmap f m = LST $ fmap f <$> getLST m

{- HLINT ignore "Functor law" -}
testFmapId :: Bool
testFmapId = check (fmap id mA) mA

{- HLINT ignore "Functor law" -}
testFmapComp :: Bool
testFmapComp = check (fmap (f . g) mA) (fmap f . fmap g $ mA)
  where f = succ ; g = pred

{- Laws
Identity: pure id <*> v = v
Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
Homomorphism: pure f <*> pure x = pure (f x)
Interchange: u <*> pure y = pure ($ y) <*> u
-}
instance Applicative (ListState st) where
  pure :: a -> ListState st a
  pure x = LST [pure x]
  
  (<*>) :: ListState st (a -> b) -> ListState st a -> ListState st b
  (LST mfs) <*> (LST mxs) = LST $ [($) <$> mf <*> mx | mf <- mfs, mx <- mxs] -- ??
  -- (LST mf) <*> (LST mx) = LST $ fmap (<*>) mf <*> mx

{- HLINT ignore "Use <$>" -}
testAppId :: Bool
testAppId = check (pure id <*> mA) mA

testAppComp :: Bool
testAppComp = check (pure (.) <*> u <*> v <*> w) (u <*> (v <*> w))
  where u = LST [state $ \s -> (pred, s^2),
                 state $ \s -> (pred . pred, s + 5)]
        v = LST [state $ \s -> (succ, s * 3),
                 state $ \s -> (succ . succ, s - 3)]
        w = mA

testAppHom :: Bool
testAppHom = check (pure f <*> pure x) (pure $ f x)
  where x = 'a'; f = succ

testAppInt :: Bool
testAppInt = check (u <*> pure y) (pure ($ y) <*> u)
  where y = 'a'
        u = LST [state $ \s -> (succ, s * 3), state $ \s -> (succ . succ, s - 3)]

{- Laws
Left identity: return a >>= k = k a
Right identity: m >>= return = m
Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
-}
instance Monad (ListState s) where
  (>>=) :: ListState st a -> (a -> ListState st b) -> ListState s b
  (LST mxs) >>= k = LST [\st0 -> let (x, st1) = mx st0 in k x | mx <- mxs] -- TODO
  -- mx st0 :: (a, st)
  -- k x :: [st -> (b, st)]
  -- st -> [st -> (b, st)] ~~ [st -> (b, st)]
  
    -- mx <- mxs
    -- my <- [state $ \st -> let x = runState mx st
    --                       in k x]
    

    -- State $ \s ->
    -- let (x, s1) = sx s
    --     State sy = k x
    -- in sy s1

-- testBindLId :: Bool
-- testBindLId = checkEqIntStrSt (return a >>= k) (k a)
--   where a = "ab"
--         k x = State $ \s -> ("c" ++ x, s + 3)

-- testBindRId :: Bool
-- testBindRId = checkEqIntStrSt (stateA >>= return) stateA

-- testBindAssoc :: Bool
-- testBindAssoc = checkEqIntStrSt ((m >>= k) >>= h) (m >>= (\x -> k x >>= h))
--   where m = stateA
--         k x = State $ \s -> ("B" ++ x, s * 2)
--         h x = State $ \s -> (x ++ "C", s^2)

test :: Bool
test = doubleWithSumTest && mATest
  && testFmapId && testFmapComp
  && testAppId && testAppComp && testAppHom && testAppInt
