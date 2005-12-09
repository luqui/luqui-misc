{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Analyze where

import Data.Array
import System.Random
import Control.Monad.State

-- A little bit of mathematical hackery here. Since x ln x goes to 
-- zero when x does, we pretend that x ln y goes to zero when x does,
-- regardless of y.
timesLog :: Double -> Double -> Double
timesLog x y = if x == 0 then 0 else x * log y

entropy :: Array Int Double -> Double
entropy dist = -sum (map (\x -> x `timesLog` x) (elems dist))

mutualInformation :: Array (Int, Int) Double -> Double
mutualInformation probs = 
    sum [ (probs ! (i,j)) `timesLog` (probs ! (i,j) / (pi i * pj j))
        | i <- [imin..imax], j <- [jmin..jmax] ]
    where
    pi i = sum [ probs ! (i,j) | j <- [jmin..jmax] ]
    pj j = sum [ probs ! (i,j) | i <- [imin..imax] ]
    ((imin, jmin), (imax, jmax)) = bounds probs

-- XXX this is only well-defined for size bits = 2^size inp
-- but I don't do any error checking :-(
binaryRule :: Array Int Int -> ([Int] -> Int)
binaryRule bits inp = binaryRule' bitsMin (bitsMax+1) inp
    where
    binaryRule' min max [] = bits ! min
    binaryRule' min max (x:xs) = 
        case x of
            0 -> binaryRule' min (avg min max) xs
            1 -> binaryRule' (avg min max) max xs
    (bitsMin, bitsMax) = bounds bits
    avg x y = (x + y) `div` 2

binaryPath :: Int -> [Int] -> [Array Int Int]
binaryPath size []     = [listArray (0,size-1) $ repeat 1]
binaryPath size (p:ps) = 
    let prev = binaryPath size ps in
    (head prev // [(p,0)]) : prev

randomRM :: (RandomGen g, Random a) => (a,a) -> State g a
randomRM rng = do
    gen <- get
    let (ret, gen') = randomR rng gen
    put gen'
    return ret

pickFrom :: (RandomGen g) => [a] -> State g (a,[a])
pickFrom xs = do
    idx <- randomRM (0, length xs - 1)
    return (xs !! idx, take idx xs ++ drop (idx+1) xs)

permute :: (RandomGen g) => [a] -> State g [a]
permute [] = return []
permute xs = do
    (r, rs) <- pickFrom xs
    fmap (r :) $ permute rs
