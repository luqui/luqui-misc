{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

module Quantum
    ( Quantum
    , qPutStr
    , runQuantum
    , qCheatInspect
    )
where

import Control.Arrow
import Data.Complex
import System.Random
import Debug.Trace

type Amp = Complex Double

data Quantum b c
    = Q (forall d. [(b,d,Amp)] -> IO [(c,d,Amp)])

getQM :: forall b c. Quantum b c -> forall d. [(b,d,Amp)] -> IO [(c,d,Amp)]
getQM (Q f) = f

instance Arrow Quantum where
    arr f = 
        Q (return . map (\ (b,d,p) -> (f b, d, p)))
    (Q f) >>> (Q g) = 
        Q $ \bds -> f bds >>= g
    first (Q f) = 
        Q $ \bds -> 
            return . map (\ (c,(d,e),p) -> ((c,d),e,p)) 
            =<< f (map (\ ((b,d),e,p) -> (b,(d,e),p)) bds)

showState :: (Show b) => [(b,d,Amp)] -> String
showState = show . map (\ (b,_,a) -> (b,a))

sumSame :: (Eq b, Show b) => [(b,d,Amp)] -> [(b,[(d,Amp)],Amp)]
sumSame = sumSame' []
    where
    sumSame' r [] = r
    sumSame' r ((b,d,p):xs) = 
        case break (\ (b',_,_) -> b == b') r of
            (pre,[])                -> sumSame' ((b,[(d,p)],p):pre) xs
            (pre,((_,ds,p'):posts)) -> sumSame' (pre ++ (b,(d,p):ds,p+p'):posts) xs

probabilize :: [(b,d,Amp)] -> [(b,d,Double)]
probabilize = map (\ (b,d,p) -> (b,d,magnitude p^2))

pick :: [(b,[(d,Amp)],Double)] -> IO [(b,d,Amp)]
pick = pick' 0 undefined
    where
    pick' accum cur [] = return $ map (\d -> (fst cur, fst d, snd d)) $ snd cur
    pick' accum cur ((b,ds,p):xs) = do
        rand <- randomRIO (0,accum+p)
        pick' (accum+p) (if rand <= p then (b,ds) else cur) xs

normalize :: [(b,d,Amp)] -> [(b,d,Amp)]
normalize xs = 
    let norm = sqrt $ sum $ map (\ (_,_,p) -> magnitude p^2) xs in
    map (\ (b,d,p) -> (b,d,p/(norm :+ 0)) ) xs

collapse :: (Eq b, Show b) => Quantum b b
collapse = Q (fmap normalize . pick . probabilize . sumSame)

qPutStr :: Quantum String ()
qPutStr = Q $ \bds -> do
    states@((b,_,_):_) <- getQM collapse bds
    putStr b
    return $ map (\ (b,d,p) -> ((),d,p)) states

qCheatInspect :: (Show b) => Quantum b b
qCheatInspect = Q $ \bds -> do
    putStrLn $ showState bds
    return bds

runQuantum :: Quantum b c -> [(b,Amp)] -> IO [(c,Amp)]
runQuantum (Q f) bs = 
    return . map (\ (c,(),p) -> (c,p)) 
    =<< f (map (\ (b,p) -> (b,(),p)) bs)
