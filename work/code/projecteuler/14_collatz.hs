{-# LANGUAGE PatternGuards #-}

import Data.List
import Data.Function

collatz :: Integer -> Integer
collatz n
    | (d,0) <- n `divMod` 2  = d
    | otherwise              = 3*n+1

collatzLength :: Integer -> Int
collatzLength n = 1 + (length $ takeWhile (/= 1) $ iterate collatz n)

maxSequence :: [Integer] -> (Integer,Int)
maxSequence ns = maximumBy (compare `on` snd) $ zip ns (map collatzLength ns)

main = print $ maxSequence [1..1000000]
