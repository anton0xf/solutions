-- parser with multiple parsing variations
module Prs where

newtype Prs s v = Prs { runPrs :: s -> String -> [((s, String), v)] }

instance Functor (Prs s) where
  fmap :: (a -> b) -> Prs s a -> Prs s b
  fmap f = Prs . (fmap . fmap . fmap . fmap) f . runPrs

instance Applicative (Prs s) where
  pure :: a -> Prs s a
  pure x = Prs $ \st chs -> [((st, chs), x)]
  
  (<*>) :: Prs s (a -> b) -> Prs s a -> Prs s b
  (Prs pf) <*> (Prs px) = Prs $ \st chs -> let
        fs = pf st chs
        ap ((st', chs'), f) = fmap f <$> px st' chs'
    in concatMap ap fs

updStPrs :: (s -> s) -> Prs s ()
updStPrs f = Prs $ \st chs -> [((f st, chs), ())]

charPrs :: Char -> Prs s Char
charPrs ch = Prs p where
  p _ "" = []
  p st (h:chs) = [((st, chs), ch) | h == ch]

anyCharPrs :: Prs s Char
anyCharPrs = Prs p where
  p _ "" = []
  p st (ch:chs) = [((st, chs), ch)]

satisfyPrs :: (Char -> Bool) -> Prs s Char
satisfyPrs pred = Prs p where
  p _ "" = []
  p st (ch:chs) = [((st, chs), ch) | pred ch]

stringPrs :: String -> Prs s String
stringPrs "" = pure ""
stringPrs (ch:chs) = (:) <$> charPrs ch <*> stringPrs chs

orPrs :: Prs s v -> Prs s v -> Prs s v
orPrs (Prs p1) (Prs p2) = Prs p where
  p st chs = let r1 = p1 st chs
                 r2 = p2 st chs
             in if null r1 then r2 else r1

variantPrs :: Prs s v -> Prs s v -> Prs s v
variantPrs (Prs p1) (Prs p2) = Prs p where
  p st chs = p1 st chs ++ p2 st chs

manyPrs :: Prs s v -> Prs s [v]
manyPrs p = ((:) <$> p <*> manyPrs p) `orPrs` pure []

many1Prs :: Prs s v -> Prs s [v]
many1Prs p = (:) <$> p <*> (manyPrs p `orPrs` pure [])

countPrs :: Int -> Prs s v -> Prs s [v]
countPrs 0 _ = pure []
countPrs n p = (:) <$> p <*> countPrs (n-1) p

pairList :: a -> a -> [a]
pairList x y = [x, y]

-- separated and enclosed by 
sepEncByPrs :: Prs s v -> Prs s v -> Prs s [v]
sepEncByPrs p sep = (:) <$> sep <*> (concat <$> manyPrs (pairList <$> p <*> sep))
