import Data.Array
import System.Random
import System

class Searchable s where
    search :: (Eq a) => s a -> a -> Bool

instance Searchable [] where
    search = flip elem

instance (Ix ix) => Searchable (Array ix) where
    search = search . elems

bench iters max coll = do
    gen <- newStdGen
    let found = length [ () | r <- take iters (randomRs (0::Int, max-1) gen)
                            , search coll r ]
    putStrLn $ show found ++ " elements found"

main = do
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
