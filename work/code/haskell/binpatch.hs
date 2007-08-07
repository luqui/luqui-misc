import Control.Monad (guard)
import Data.Maybe (fromJust)
import Data.List (nub)
import System (getArgs)

type X = [Bool]
len = 3

untablify :: (Eq a) => [(a,a)] -> a -> a
untablify as a = fromJust $ lookup a as

merges :: X -> X -> X -> [X]
merges a b c = do
    f <- funcs
    guard $ (f a) == b
    g <- funcs
    guard $ (g a) == c
    if f (g a) == g (f a)
        then [f (g a)]
        else []
    where
    funcs :: [X -> X]
    funcs =
        map untablify $ mapM (\x -> xs >>= return . (,) x) xs
        
    xs = sequence $ replicate len bs
    bs = [False,True]

merge :: X -> X -> X -> [X]
merge a b c = nub $ merges a b c

main :: IO ()
main = do
    [a,b,c] <- fmap (map rbs) getArgs
    mapM_ print $ merge a b c
    where
    rbs :: String -> X
    rbs = map (== '1')
