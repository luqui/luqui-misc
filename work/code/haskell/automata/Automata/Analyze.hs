{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Analyze where

import Data.Array

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
