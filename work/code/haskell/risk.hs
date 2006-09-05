import System.Environment (getArgs)
import qualified List

dice = [1..6]

riskSort :: [Int] -> [Int] -> Int
riskSort as ds = riskSort' (reverse $ List.sort as) (reverse $ List.sort ds)
	where
	riskSort' [] _ = 0
	riskSort' _ [] = 0
	riskSort' (a:as) (d:ds) = (if a > d then 1 else -1) + riskSort' as ds

dicen :: Int -> [[Int]]
dicen 1 = map return dice
dicen n = do
	prev <- dicen (n-1)
	fst <- dice
	return (fst : prev)

cases :: Int -> Int -> [Int]
cases a d = do
	as <- dicen a
	ds <- dicen d
	return $ riskSort as ds

prob :: Int -> Int -> Double
prob a d = fromIntegral (sum cs) / fromIntegral (length cs)
	where
	cs = cases a d

main :: IO ()
main = do
	[a,d] <- getArgs
	print $ prob (read a) (read d)
