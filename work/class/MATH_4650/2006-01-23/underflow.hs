underflow :: Double
underflow = until (\x -> (1 + x) - 1 == 0) (/ 2) 1

main :: IO ()
main = do
    putStrLn $ "The maximum number at which underflow occurs is " ++ show underflow
