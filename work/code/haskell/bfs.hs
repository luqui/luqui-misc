data Tree a = Branch { value :: a, children :: [Tree a] }

ap :: (a -> b -> c) -> (a -> b) -> a -> c
ap f g x = f x (g x)

-- Breadth-first search
bfs :: Tree a -> [a]
bfs tree = map value $ bfs' [tree]
	where
        bfs' [] = []
        bfs' xs = ap (++) (bfs' . concatMap children) xs

-- Duh-first search
dfs :: Tree a -> [a]
dfs tree = map value $ dfs' [tree]
        where
        dfs' xs = concatMap (ap (:) (dfs' . children)) xs
