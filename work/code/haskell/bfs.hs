data Tree a = Branch { value :: a, children :: [Tree a] }

-- Breadth-first search
bfs :: Tree a -> [a]
bfs tree = bfs' [tree]
	where
	bfs' [] = []
	bfs' trees = map value trees ++ (bfs' (concatMap children trees))
