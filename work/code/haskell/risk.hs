{-# OPTIONS_GHC -fbang-patterns #-}

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

avg :: [Int] -> Double
avg = avg' 0 0
    where
    avg' :: Integer -> Integer -> [Int] -> Double
    avg' tot ct [] = fromIntegral tot / fromIntegral ct
    avg' (!tot) (!ct) (x:xs) = avg' (tot+fromIntegral x) (ct+1) xs

prob :: Int -> Int -> Double
prob a d = avg (cases a d)

main :: IO ()
main = do
	[a,d] <- getArgs
	print $ prob (read a) (read d)
