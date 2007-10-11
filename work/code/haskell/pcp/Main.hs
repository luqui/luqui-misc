module Main (main) where

import Solver
import System.IO
import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception (evaluate)
import Data.List (intersperse)

ask :: (Read a, Show a) => String -> a -> IO a
ask q def = do
    putStr $ q ++ " (" ++ show def ++ ")? "
    ln <- getLine
    if null ln 
        then return def 
        else return (read ln)

loop :: IO () -> IO ()
loop a = a >> loop a

formatPcp :: Pcp -> String
formatPcp pcp = formatLine fst ++ "\n" ++ formatLine snd ++ "\n"
    where
    width = maximum (map (\ (as,bs) -> max (length as) (length bs)) pcp) + 1
    formatLine elem = concat $ intersperse " " $ map (justify . concatMap show . elem) pcp
    justify s = s ++ replicate (width - length s) ' '


forkEnumerator :: MVar [Pcp] -> IO ThreadId
forkEnumerator toEnumerate = 
    forkIO $ loop $ do
        v <- takeMVar toEnumerate
        putStrLn "Computing..."
        case v of
            []     -> return ()
            (x:xs) -> do
                putStr $ formatPcp x
                putStrLn "--"
                tryPutMVar toEnumerate xs
                return ()

execUI :: [[Pcp]] -> IO ()
execUI pcps = do
    steps <- ask "How many steps" 5
    toEnumerate <- newEmptyMVar
    enumeratorThread <- forkEnumerator toEnumerate

    putMVar toEnumerate (pcps !! steps)
    getLine
    killThread enumeratorThread

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    topn    <- ask "Max pieces on top" 3
    botn    <- ask "Max pieces on bottom" 3
    npanels <- ask "How many panels" 4
    
    let pcps = allPcps [0,1] topn botn npanels
    let solution = findProblems pcps

    loop (execUI solution)
