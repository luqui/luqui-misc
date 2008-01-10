module Fregl.LinearSplit
    ( LinearSplit
    , newLinearSplit
    , readLinearSplit
    , linearSplit
    )
where

import Fregl.Splittable
import Control.Concurrent.STM
import System.IO.Unsafe

data LinearSplit a = LinearSplit (TVar [a]) (IO a)

makeReader :: TVar [a] -> IO (IO a)
makeReader xsvar = do
    cache <- newTVarIO Nothing
    return $ atomically $ do
        c <- readTVar cache
        case c of
             Just x -> return x
             Nothing -> do
                 (x:xs) <- readTVar xsvar
                 writeTVar xsvar xs
                 writeTVar cache (Just x)
                 return x

newLinearSplit :: [a] -> IO (LinearSplit a)
newLinearSplit xs = do
    xsvar <- newTVarIO xs
    reader <- makeReader xsvar
    return $ LinearSplit xsvar reader

readLinearSplit :: LinearSplit a -> IO a
readLinearSplit (LinearSplit _ act) = act

linearSplit :: LinearSplit a -> IO (LinearSplit a, LinearSplit a)
linearSplit (LinearSplit xsvar act) = do
    a <- makeReader xsvar
    b <- makeReader xsvar
    return (LinearSplit xsvar a, LinearSplit xsvar b)

instance Splittable (LinearSplit a) where
    split = unsafePerformIO . linearSplit
