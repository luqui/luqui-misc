{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Analyze where

import Data.Array
import qualified Data.Map as Map
import System.Random
import Control.Monad.State

import Automata.Simulate


-- Just a convenience function to divide two integers to get a fractional
a ./ b = fromIntegral a / fromIntegral b


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


count :: (Ord a) => [a] -> Map.Map a Int
count []     = Map.empty
count (x:xs) = Map.insertWith (+) x 1 (count xs)


makeDist :: (Integral b, Fractional c) => [b] -> Array Int c
makeDist xs = listArray (0, length xs - 1) $ map ((/ total) . fromIntegral) xs
    where
    total = fromIntegral $ sum xs


count2 :: (Ord a, Ord b) => [(a,b)] -> Map.Map a (Map.Map b Int)
count2 []    = Map.empty
count2 ((a,b):xs) = Map.insertWith (Map.unionWith (+)) a (Map.singleton b 1) (count2 xs)


makeDist2 :: (Ord a, Ord b, Integral i, Fractional f) 
          => Map.Map a (Map.Map b i) -> Array (Int,Int) f
makeDist2 table =
    populateArray [ ((xmap Map.! x, ymap Map.! y), table Map.! x Map.! y) 
                  | x <- Map.keys table
                  , y <- Map.keys (table Map.! x) ]
    where
    (sizex, xmap) = intMap (Map.keys table)
    (sizey, ymap) = intMap (concatMap Map.keys (Map.elems table))
    total         = sum (concatMap Map.elems (Map.elems table))
    
    intMap []     = (0, Map.empty)
    intMap (x:xs) = 
        let (new, prev) = intMap xs in
        if x `Map.member` prev
            then (new, prev)
            else (new+1, Map.insert x new prev)

    populateArray [] = listArray ((0,0), (sizex-1, sizey-1)) (repeat 0)
    populateArray ((key,amt):rest) =
        let prev = populateArray rest in
        prev // [ (key, (prev ! key) + amt ./ total) ]


automatonEntropy :: (Ord a, Topology c, Configuration c)
                 => ([a] -> a) -> c a -> Int -> Double
automatonEntropy f aut iters = 
    entropy $ makeDist $ Map.elems $ Map.unionsWith (+) $ 
        map count $ take iters autiter
    where
    autiter = map cells $ iterate (update f) aut


automatonSpatialMI :: (Ord a, Topology c, Configuration c)
                   => ([a] -> a) -> c a -> Int -> (Int,Int) -> Double
automatonSpatialMI f aut iters (px,py) =
    mutualInformation $ makeDist2 $ count2 $ map (\x -> (x !! px, x !! py)) $ take iters autiter 
    where
    autiter = map cells $ iterate (update f) aut
    

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

