import qualified List

mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f (x,y) = (f x, y)

data Prob a = Prob { runProb :: [(Double, a)] }
	deriving Show

instance Monad Prob where
	Prob ms >>= f = 
		Prob $ concatMap (\ (p, x) -> map (mapFst (* p)) $ runProb $ f x) ms
	return x = Prob [(1,x)]

uniform :: [a] -> Prob a
uniform xs = Prob $ map (\x -> (prob,x)) xs
	where
	prob = 1 / fromIntegral (length xs)

distribution :: [(Double, a)] -> Prob a
distribution = Prob

merge :: (Eq a) => Prob a -> Prob a
merge (Prob []) = Prob []
merge (Prob ((prob, elem):xs)) = 
	let (matches, nonmatches) = List.partition ((== elem) . snd) xs in
		Prob ((prob + sum (map fst matches), elem) : runProb (merge (Prob nonmatches)))

tripProb :: Prob Bool
tripProb = do
	rolls <- mapM (const $ uniform [1..6]) [1..5]
	if length (filter (\x -> length (filter (== x) rolls) >= 3) rolls) > 0
		then return True
		else return False
