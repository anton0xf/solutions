{- https://stepik.org/lesson/38578/step/5?unit=20503
4.1.5. Трансформер WriterT -}

{- Предположим, что мы дополнительно реализовали строгую версию аппликативного функтора Writer: -}

newtype Writer w a = Writer { runWriter :: (a, w) }
newtype StrictWriter w a = StrictWriter { runStrictWriter :: (a, w) }

instance Functor (Writer w) where
  fmap :: (a -> b) -> Writer w a -> Writer w b
  fmap f = Writer . updater . runWriter
    where updater ~(x, log) = (f x, log)

instance Functor (StrictWriter w) where
  fmap :: (a -> b) -> StrictWriter w a -> StrictWriter w b
  fmap f = StrictWriter . updater . runStrictWriter
    where updater (x, log) = (f x, log)

instance Monoid w => Applicative (Writer w) where
  pure :: Monoid w => a -> Writer w a
  pure x  = Writer (x, mempty)
  
  (<*>) :: Monoid w => Writer w (a -> b) -> Writer w a -> Writer w b
  f <*> v = Writer $ updater (runWriter f) (runWriter v)
    where updater ~(g, w) ~(x, w') = (g x, w <> w')

instance Monoid w => Applicative (StrictWriter w) where
  pure :: Monoid w => a -> StrictWriter w a
  pure x  = StrictWriter (x, mempty)
  
  (<*>) :: Monoid w => StrictWriter w (a -> b) -> StrictWriter w a -> StrictWriter w b
  f <*> v = StrictWriter $ updater (runStrictWriter f) (runStrictWriter v)
    where updater (g, w) (x, w') = (g x, w <> w')

{- и определили такие вычисления: -}

actionLazy :: Writer String Integer
actionLazy = Writer (42,"Hello!")

actionStrict :: StrictWriter String Integer
actionStrict = StrictWriter (42,"Hello!")

{- Какие из следующих вызовов приведут к расходимостям?
Выберите все подходящие ответы из списка:

fst . runWriter $ take 5 <$> sequenceA (repeat actionLazy)
fst . runStrictWriter $ take 5 <$> sequenceA (repeat actionStrict)
runWriter $ take 5 <$> sequenceA (repeat actionLazy)
runStrictWriter $ take 5 <$> sequenceA (repeat actionStrict)
 -}

{-
repeat :: a -> [a]
repeat x = xs where xs = x : xs

sequenceA :: Applicative f => t (f a) -> f (t a)
sequenceA = traverse id

traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
traverse :: Applicative f => (a -> f b) -> [a] -> f [b]
traverse f = List.foldr cons_f (pure [])
  where cons_f x ys = liftA2 (:) (f x) ys

sequenceA :: Applicative f => [f a] -> f [a]
sequenceA = foldr (liftA2 (:)) (pure [])

sequenceA :: Applicative f => [f a] -> f [a]
sequenceA = foldr (liftA2 (:)) (pure [])

sequenceA :: Writer f => [f a] -> f [a]
sequenceA :: Monoid w => [Writer w a] -> Writer w [a]
sequenceA = foldr (liftA2 (:)) (Writer ([], mempty))

liftA2 :: (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)

fst . runWriter $ head <$> sequenceA (repeat actionLazy)
== fst (runWriter (head <$> sequenceA (repeat actionLazy)))
== fst (runWriter (head <$> sequenceA (xs where xs = actionLazy : xs))
== fst (runWriter (head <$> sequenceA (xs where xs = Writer (42, "Hello!") : xs))
== fst (runWriter (head <$>
    foldr (liftA2 (:)) (Writer ([], mempty))
          (xs where xs = Writer (42, "Hello!") : xs))
== fst (runWriter (head <$>
    (liftA2 (:)) (Writer (42, "Hello!"))
        (foldr (liftA2 (:)) (Writer ([], mempty))
               (xs where xs = Writer (42, "Hello!") : xs))))
== fst (runWriter (head <$>
    (fmap (:) (Writer (42, "Hello!"))) <*>
        (foldr (liftA2 (:)) (Writer ([], mempty))
               (xs where xs = Writer (42, "Hello!") : xs))))
== fst (runWriter (head <$>
    (Writer ((42 :), "Hello!")) <*>
        (foldr (liftA2 (:)) (Writer ([], mempty))
               (xs where xs = Writer (42, "Hello!") : xs))))

  (<*>) :: Monoid w => Writer w (a -> b) -> Writer w a -> Writer w b
  f <*> v = Writer $ updater (runWriter f) (runWriter v)
    where updater ~(g, w) ~(x, w') = (g x, w <> w')

== fst (runWriter (head <$>
    Writer ((42 :) x, "Hello!" <> w')
        where ~(x, w') = (foldr (liftA2 (:)) (Writer ([], mempty))
                                (xs where xs = Writer (42, "Hello!") : xs))))
== fst (runWriter (Writer (head (42 : x), "Hello!" ++ w')
        where ~(x, w') = (foldr (liftA2 (:)) (Writer ([], mempty))
                                (xs where xs = Writer (42, "Hello!") : xs))))
== fst ((head (42 : x), "Hello!" ++ w')
        where ~(x, w') = (foldr (liftA2 (:)) (Writer ([], mempty))
                                (xs where xs = Writer (42, "Hello!") : xs)))
== fst (head (42 : x), "Hello!" ++ w')
       where ~(x, w') = (foldr (liftA2 (:)) (Writer ([], mempty))
                               (xs where xs = Writer (42, "Hello!") : xs))
== head (42 : x)
       where ~(x, w') = (foldr (liftA2 (:)) (Writer ([], mempty))
                               (xs where xs = Writer (42, "Hello!") : xs))
== 42
-}
