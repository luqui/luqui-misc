import System
import System.IO
import Data.List

divides :: (Integral a) => a -> a -> Bool
divides a b = b `mod` a == 0

primesFrom :: (Integral a) => a -> [a]
primesFrom 2 = 2:primesFrom 3   -- bootstrap
primesFrom from =
    if flip any possiblePrimes (`divides` from)
        then primesFrom (from+2)
        else from : primesFrom (from+2) 
    where
    possiblePrimes = takeWhile (\x -> fromIntegral x <= sqrt (fromIntegral from)) $ primesFrom 2

primes :: (Integral a) => [a]
primes = primesFrom 2

isPrime :: (Integral a) => a -> Bool
isPrime n
	| n < 2     = False
	| otherwise = last (takeWhile (<= n) primes) == n

seqDiff :: (Num a) => [a] -> [a]
seqDiff (x:x':xs) = (x' - x) : seqDiff (x':xs)
seqDiff [_] = []

primeDiff :: (Integral a) => [a]
primeDiff = seqDiff primes

agreeBeginning :: (Eq a) => [a] -> [a] -> Int
agreeBeginning [] (_:_) = 0
agreeBeginning (_:_) [] = 0
agreeBeginning (x:xs) (y:ys) = 
    if x == y
        then 1 + agreeBeginning xs ys
        else 0

printList :: (Show a) => [a] -> IO ()
printList xs = mapM_ print xs

main :: IO ()
main = do
	hSetBuffering stdout NoBuffering
	print $ filter isPrime $ map sum $ inits primes
