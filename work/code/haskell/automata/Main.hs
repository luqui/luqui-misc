{-# OPTIONS_GHC -fglasgow-exts #-}

module Main where

import System
import Control.Monad.State
import Automata.Simulate
import qualified Automata.Simulate.Circle as Circle
import Automata.Analyze

randomBinList :: Int -> IO [Int]
randomBinList len =
    mapM (randomRIO (0,1)) [1..len]

main :: IO ()
main = do
    [radStr, lenStr] <- getArgs
    let rad       = read radStr
        len       = read lenStr
        ruleBits  = 2^(2*rad + 1)

    init <- randomBinList len
    let circle = Circle.makeCircle neighbors init

    perm <- do gen <- getStdGen
               (perms, gen') = runState (permute [0..ruleBits-1])
               setStdGen gen'
               return perms
               
    let path = binaryPath ruleBits perm
