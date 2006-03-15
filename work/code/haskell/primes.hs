import System

divides :: (Integral a) => a -> a -> Bool
divides a b = b `mod` a == 0

primes :: (Integral a) => a -> [a]
primes 2 = 2:primes 3   -- bootstrap
primes from =
    if flip any possiblePrimes (`divides` from)
        then primes (from+2)
        else from : primes (from+2) 
    where
    possiblePrimes = takeWhile (\x -> fromIntegral x <= sqrt (fromIntegral from)) $ primes 2

seqDiff :: (Num a) => [a] -> [a]
seqDiff (x:x':xs) = (x' - x) : seqDiff (x':xs)
seqDiff [_] = []

primeDiff :: (Integral a) => [a]
primeDiff = seqDiff $ primes 2

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
    args <- getArgs
    case args of
        []    -> printList $ primes 2
        [num] -> printList $ take (read num) (primes 2)
        _     -> error "Usage: primes [number]"
