import Data.Array
import Data.Foldable (toList)
import System.Random
import System


search arr x = x `elem` toList arr

bench iters max coll = do
    gen <- newStdGen
    let found = length [ () | r <- take iters (randomRs (0::Int, max-1) gen)
                            , search coll r ]
    putStrLn $ show found ++ " elements found"

main' = do
    [mode, sizeS, maxS, itersS] <- getArgs
    let size = read sizeS ; max = read maxS ; iters = read itersS
    gen <- newStdGen
    case mode of
        "array" -> do
            let arr = listArray (0::Int,size-1) (randomRs (0::Int, max-1) gen)
            bench iters max arr
        "list" -> do
            let list = take size (randomRs (0::Int, max-1) gen)
            bench iters max list

-- hax!!1
main = catch main' $ \e -> do
    putStrLn "Usage: search_g <array|list> size max iters"
