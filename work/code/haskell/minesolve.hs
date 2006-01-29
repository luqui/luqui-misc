{-# OPTIONS_GHC -fglasgow-exts #-}

import Control.Monad.State as State
import Text.Regex

type Equation = ([Int], Int)

numVars :: [Equation] -> Int
numVars = maximum . map (length . fst)

metric :: [Equation] -> [Int] -> Int
metric eqs xs = 
    sum $ map localMetric eqs
    where
    localMetric :: Equation -> Int
    localMetric (inp, outp) = abs (outp - sum (zipWith (*) inp xs))

binaries :: Int -> [[Int]]
binaries 0 = [[]]
binaries n = do
    bn' <- binaries (n-1)
    bit <- [0,1]
    return (bit:bn')
    
solve :: [Equation] -> [[Int]] -> [[Int]]
solve eqs = filter ((== 0) . metric eqs)

data Check = Y Int | N

instance Show Check where
    show (Y i) = show i
    show N     = "?"

convolve :: [[Int]] -> [Check]
convolve xs = foldr combine (map Y (head xs)) (tail xs)
    where
    combine :: [Int] -> [Check] -> [Check]
    combine = zipWith combine1
    combine1 :: Int -> Check -> Check
    combine1 i (Y j) = if i == j then Y i else N
    combine1 i N     = N

main :: IO ()
main = do
    putStrLn "Enter each equation, followed by a single '.' when done."
    eqs <- readEq
    let sols = solve eqs (binaries (numVars eqs))
    mapM_ print sols
    putStrLn "--"
    print (convolve sols)
    where
    readEq = do
        let rx = mkRegex "(([0-9] *)+) *= *([0-9]+)"
        line <- getLine
        if line == "."
            then return []
            else case matchRegex rx line of
                Nothing     -> putStrLn "Syntax error" >> readEq
                Just [xs,_,y] -> do
                    rest <- readEq
                    return $ (map read (words xs), read y) : rest
