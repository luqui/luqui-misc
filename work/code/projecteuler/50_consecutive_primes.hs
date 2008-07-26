import qualified Data.Set as Set

isPrime :: Int -> Bool
isPrime n = all (\k -> n `mod` k /= 0) candidates
    where
    candidates = takeWhile (<= upperBound) primes
    upperBound = floor (sqrt (fromIntegral n))

primes = 2:filter isPrime [3,5..]

primeSums n = map (sum . take n) $ iterate tail primes

solutions n = filter isPrime $ takeWhile (< 1000000) $ primeSums n
