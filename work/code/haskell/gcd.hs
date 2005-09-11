-- For cryptography homework

import System

vgcd :: Integer -> Integer -> IO Integer
vgcd a 0 = return a
vgcd a b = do let q = a `quot` b
                  r = a `mod` b
              putStrLn $ show a ++ " = " 
                            ++ show q ++ " * " ++ show b 
                            ++ " + " ++ show r
              vgcd b r

main :: IO ()          
main = do
    [sa, sb] <- getArgs
    result <- vgcd (read sa) (read sb)
    putStrLn $ "gcd = " ++ show result
