{-# OPTIONS_GHC -fbang-patterns #-}

import HalfRef
import qualified System.Random as Random

makeBigValue :: IO [Int]
makeBigValue = do
    val <- fmap (take 100000 . Random.randoms) Random.newStdGen
    putStrLn $ "Sum = " ++ show (sum val)
    return val

askBigs xs = do
    putStrLn "Push enter to allocate another"
    getLine
    nextBig <- makeBigValue
    (lk,rk) <- makeHalfRef nextBig
    askBigs (lk:xs)


main :: IO ()
main = askBigs []

