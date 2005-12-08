cyclePeriod :: (Eq a) => [a] -> Int
cyclePeriod xs = until (\i -> and (zipWith (==) xs (drop i $ cycle xs)))
                       (+1) 1

shift :: Int -> [a] -> [a]
shift n xs = drop n xs ++ take n xs

allBinaries :: Int -> [[Int]]
allBinaries 1 = [[0],[1]]
allBinaries n = do
    prev <- allBinaries (n-1)
    [0:prev, 1:prev]

shequiv :: (Eq a) => [a] -> [a] -> Bool
shequiv xs ys = length xs == length ys && 
                any (== ys) (map (\n -> shift n xs) [0..length xs-1])

numCycles :: Int -> Int
numCycles x = length $ numCycles' (allBinaries x)
    where
    numCycles' [] = []
    numCycles' (a:as) = 
        let pcycs = numCycles' as in
        if cyclePeriod a == x && all (not . shequiv a) pcycs
            then a:pcycs
            else pcycs
