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

liftMA :: (Monad m) =>  ([a] -> b) -> [m a] -> m b
liftMA f ms =
    liftM f (liftJoin ms)
    where
    liftJoin :: (Monad m) => [m a] -> m [a]
    liftJoin []     = return []
    liftJoin (m:ms) = liftM2 (:) m (liftJoin ms)

checkEqs :: [Equation] -> [Int] -> Bool
checkEqs eqs pfx = 
    all checkEq eqs
    where
    checkEq :: Equation -> Bool
    checkEq (xs, y) = 
        let val0 = sum (zipWith (*) xs (pfx ++ repeat 0))
            val1 = sum (zipWith (*) xs (pfx ++ repeat 1)) in
        case () of
            () | val0 > y -> False
               | val1 < y -> False
               | otherwise -> True

pruneSolve :: [Equation] -> Int -> [Int] -> [[Int]]
pruneSolve eqs 0 pfx = if metric eqs pfx == 0 then [pfx] else []
pruneSolve eqs n pfx = 
    if checkEqs eqs pfx
        then pruneSolve eqs (n-1) (pfx ++ [0]) ++ pruneSolve eqs (n-1) (pfx ++ [1])
        else []

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
    let sols = pruneSolve eqs (numVars eqs) []
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
