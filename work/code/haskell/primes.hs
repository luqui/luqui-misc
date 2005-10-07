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

printList :: (Show a) => [a] -> IO ()
printList xs = mapM_ (putStrLn . show) xs

main :: IO ()
main = do
    args <- getArgs
    case args of
        []    -> printList $ primes 2
        [num] -> printList $ take (read num) (primes 2)
        _     -> error "Usage: primes [number]"
