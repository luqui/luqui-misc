import Data.List
import System

type Perm = [Int]

each :: [a] -> [(a,[a])]
each [] = []
each (x:xs) = (x,xs) : [ (y,x:ys) | (y,ys) <- each xs ]

symmetricGroup :: Int -> [Perm]
symmetricGroup ord = permute [0..ord-1]
    where
    permute :: [Int] -> [Perm]
    permute [] = [[]]
    permute xs = do
        (first, rest) <- each xs
        prest <- permute rest
        return $ first : prest

compose :: Perm -> Perm -> Perm
compose x y = map (x !!) y

isAbelian :: [Perm] -> Bool
isAbelian xs = and $ do
    x <- xs
    y <- xs
    return $ x `compose` y == y `compose` x

subgroups :: [Perm] -> [[Perm]]
subgroups [] = [[]]
subgroups (x:xs) = do
    subs <- subgroups xs
    [x:subs, subs]

maxAbelianSubgroup :: [Perm] -> [Perm]
maxAbelianSubgroup p = maximumBy (\x y -> length x `compare` length y)
                                 (filter isAbelian $ subgroups p)

main :: IO ()
main = do
    [snum] <- getArgs
    let num = read snum
    print $ maxAbelianSubgroup (symmetricGroup num)
