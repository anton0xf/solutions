headOrZero :: Num a => [a] -> a
headOrZero [] = 0
headOrZero (x : _) = x

safeTail :: [a] -> [a]
safeTail [] = []
safeTail (_ : xs) = xs

sum3 :: Num a => [a] -> [a] -> [a] -> [a]
sum3 [] [] [] = []
sum3 xs ys zs = headOrZero xs + headOrZero ys + headOrZero zs
  : sum3 (safeTail xs) (safeTail ys) (safeTail zs)
