{-
https://stepik.org/lesson/12321/step/8?unit=2785

Воспользовавшись функциями map и concatMap, определите функцию perms,
которая возвращает все перестановки,
которые можно получить из данного списка, в любом порядке.

GHCi> perms [1,2,3]
[[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]]

Считайте, что все элементы в списке уникальны,
и что для пустого списка имеется одна перестановка.
-}

perms :: [a] -> [[a]]
perms [] = [[]]
perms (x : xs) = concatMap (insert x) (perms xs)
  where
    insert :: a -> [a] -> [[a]]
    insert x [] = [[x]]
    insert x (y:ys) = (x:y:ys) : map (y:) (insert x ys)
