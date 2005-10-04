-- For cryptography homework

import System

vgcd :: Integer -> Integer -> IO Integer
vgcd a 0 = return a
vgcd a b = do let q = a `quot` b
                  r = a `mod` b
              putStrLn $ show a ++ " = " ++ show q ++ " * " 
                                ++ show b ++ " + " ++ show r
              vgcd b r

bigits :: Integer -> [Integer]
bigits 0 = []
bigits num = if num `mod` 2 == 0 
                 then 0 : bigits (num `div` 2)
                 else 1 : bigits (num `div` 2)

modpow :: Integer -> Integer -> Integer -> Integer
modpow num pow modulus = modpow' (bigits pow) num
    where
    modpow' :: [Integer] -> Integer -> Integer
    modpow' [] _ = 1
    modpow' (bit:bits) cur =
        let dbl = (cur ^ 2) `mod` modulus in
            if bit == 1
                then (cur * modpow' bits dbl) `mod` modulus
                else modpow' bits dbl

main :: IO ()          
main = do
    [sa, sb] <- getArgs
    result <- vgcd (read sa) (read sb)
    putStrLn $ "gcd = " ++ show result
