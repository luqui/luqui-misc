{-# OPTIONS_GHC -fglasgow-exts #-}

module Main where

import System
import System.IO
import System.Random
import Control.Monad.State
import Data.Array
import Automata.Simulate
import qualified Automata.Simulate.Circle as Circle
import Automata.Analyze

randomBinList :: Int -> IO [Int]
randomBinList len =
    mapM (const $ randomRIO (0,1)) [1..len]

printStats :: (Topology c, Configuration c) 
           => c Int -> Array Int Int -> IO ()
printStats circle ruledesc = do
    let rule = binaryRule ruledesc
        entropy' = automatonEntropy rule circle 1000           -- XXX number of iterations
        mi       = automatonSpatialMI rule circle 1000 (0,10)  -- XXX separation distance
        lambda   = sum (elems ruledesc) ./ length (elems ruledesc)
    putStrLn $ show lambda ++ "\t" ++ show entropy' ++ "\t" ++ show mi

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering

    [radStr, lenStr] <- getArgs
    let rad       = read radStr
        len       = read lenStr
        ruleBits  = 2^(2*rad + 1)

    init <- randomBinList len
    let circle = Circle.makeCircle rad init

    perm <- do gen <- getStdGen
               let (perm, gen') = runState (permute [0..ruleBits-1]) gen
               setStdGen gen'
               return perm
    
    let path = binaryPath ruleBits perm

    mapM_ (printStats circle) path
