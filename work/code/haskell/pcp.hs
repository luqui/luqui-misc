import Data.List (partition)
import System (getArgs)

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

------- Iterative solution ------------
haltsInNSteps :: Int -> Pcp -> Bool
haltsInNSteps n pcp = haltsInNSteps' n [emptyCfg]
    where
    haltsInNSteps' 0 []   = True
    haltsInNSteps' 0 cfgs = any cfgGood cfgs
    haltsInNSteps' n []   = False
    haltsInNSteps' n cfgs =
        not (any cfgGood cfgs) &&
        (haltsInNSteps' (n-1) $ concatMap (dijkstep pcp) cfgs)
---------------------------------------

data SolType = Iterative | Simultaneous | Test
    deriving Read

findProblems :: SolType -> [Pcp] -> [[Pcp]]
findProblems Iterative pcps    = map (\n -> filter (haltsInNSteps n) pcps) [0..]
findProblems Simultaneous pcps = haltingFilter pcps

allStrings :: [Piece] -> Int -> [[Piece]]
allStrings pieces 0 = [[]]
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

main :: IO ()
main = do
    args <- getArgs
    let topn    = read $ args !! 0
        botn    = read $ args !! 1
        npanels = read $ args !! 2
        steps   = read $ args !! 3
        soltype = read $ args !! 4

    let pcps = allPcps [0,1] topn botn npanels
    mapM_ print $ findProblems soltype pcps !! steps


sequencer :: [[a]] -> [[a]]
sequencer = map reverse . sequencer' . reverse
    where
    sequencer' [] = return []
    sequencer' (x:xs) = do
        ts <- sequencer' xs
        t <- x
        return (t:ts)
