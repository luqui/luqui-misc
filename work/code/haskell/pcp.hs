{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.List (partition)
import Control.Monad.State
import System.IO

type Piece = Int

type Cfg = ([Piece],[Piece])
type Pcp = [Cfg]

emptyCfg :: Cfg
emptyCfg = ([],[])

appendCfg :: Cfg -> Cfg -> Cfg
appendCfg (as,bs) (as',bs') = (as ++ as', bs ++ bs')

dijkstep :: Pcp -> Cfg -> [Cfg]
dijkstep pcp cfg = filter cfgViable $ map (appendCfg cfg) pcp

cfgGood :: Cfg -> Bool
cfgGood (as,bs) = as == bs

cfgViable :: Cfg -> Bool
cfgViable (as,bs) = and $ zipWith (==) as bs


------- Simultaneous solution ---------
beaverFilter :: (a -> [Bool]) -> [a] -> [[a]]
beaverFilter f = map (map fst) . beaverFilter' . map (\x -> (x,f x))
    where
    beaverFilter' xs =
        let (ys,ns) = partition (halted . snd) xs in
            ys : beaverFilter' (map (\ (x,bs) -> (x,tail bs)) ns)
    halted bs = null bs || head bs

haltingFilter :: [Pcp] -> [[Pcp]]
haltingFilter = beaverFilter hasHalted
    where
    hasHalted pcp =
        let steps = tail $ iterate (concatMap (dijkstep pcp)) [emptyCfg] in 
            map (any cfgGood) steps 
---------------------------------------

findProblems :: [Pcp] -> [[Pcp]]
findProblems pcps = haltingFilter pcps


allStrings :: [Piece] -> Int -> [[Piece]]
allStrings pieces 0 = return []
allStrings pieces n = do
    p <- pieces
    s <- allStrings pieces (n-1)
    return (p:s)

allCfgs :: [Piece] -> Int -> Int -> [Cfg]
allCfgs pieces topn botn = do
    topn' <- [1..topn]
    botn' <- [1..botn]
    top <- allStrings pieces topn'
    bot <- allStrings pieces botn'
    return (top,bot)

allPcps :: [Piece] -> Int -> Int -> Int -> [Pcp]
allPcps pieces topn botn cfgs =
    sequencer (replicate cfgs $ allCfgs pieces topn botn)

ask :: (Read a, Show a) => String -> a -> IO a
ask q def = do
    putStr $ q ++ " (" ++ show def ++ ")? "
    ln <- getLine
    if null ln 
        then return def 
        else return (read ln)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    topn    <- ask "Max pieces on top" 3
    botn    <- ask "Max pieces on bottom" 3
    npanels <- ask "How many panels" 4
    steps   <- ask "How many steps for a good solution" 5
    
    let pcps = allPcps [0,1] topn botn npanels
    mapM_ print $ findProblems pcps !! steps


sequencer :: (Monad m) => [m a]-> m [a]
sequencer [] = return []
sequencer (x:xs) = do
    ts <- sequencer xs
    t <- x
    return (t:ts)
