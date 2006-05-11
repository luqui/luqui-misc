import Control.Monad.Writer

divides :: Integer -> Integer -> Bool
divides m n = n `mod` m == 0

nextPrime :: [Integer] -> Integer -> Integer
nextPrime ps n =
	if any (`divides` n) possiblePrimes
		then nextPrime ps (n+1)
		else n
	where
	possiblePrimes = takeWhile (<= upperBound) ps
	upperBound = ceiling $ sqrt $ fromIntegral n

primes :: [Integer]
primes = primes' [] 2
	where 
	primes' ps n = 
		let np = nextPrime ps n in
		np : primes' (ps ++ [np]) (np+1)

order :: Integer -> Integer -> Integer -> Integer
order 1 _ _ = 1
order a m n = 1 + order ((a*m) `mod` n) m n

prim2 :: [Integer]
prim2 = filter (\n -> order 2 2 n == n - 1) (tail primes)

main :: IO ()
main = mapM_ print prim2
