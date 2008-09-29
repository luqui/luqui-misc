module Temporal.IVar 
    ( IVar, new, write
    , Reader, read, merge
    , nonblocking, blocking, combination
    , timed
    )
where

import Prelude hiding (read)
import Control.Concurrent
import Control.Applicative
import Control.Monad (ap)
import System.Time

newtype IVar a = IVar (MVar a)

new :: IO (IVar a)
new = IVar <$> newEmptyMVar

write :: IVar a -> a -> IO ()
write (IVar var) x = putMVar var x

-- combinationRead returns either Left v, if the value is already available, or
-- Right v', where v' is a blocking action
data Reader a = Reader { combination :: IO (Either a (IO a)) }

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f g = either (Left . f) (Right . g)

instance Functor Reader where
    fmap f (Reader io) = Reader (fmap (mapEither f (fmap f)) io)
    
instance Monad Reader where
    return = Reader . return . Left
    m >>= f = Reader $ do
        choice <- combination m
        case choice of
            Left x -> combination (f x)
            Right io -> return . Right $ do
                x <- io
                either return id =<< combination (f x)

instance Applicative Reader where
    pure = return
    (<*>) = ap

read :: IVar a -> Reader a
read (IVar m) = Reader $ do
    empty <- isEmptyMVar m
    if empty
        then return . Right $ readMVar m
        else Left <$> readMVar m

merge :: Reader a -> Reader a -> Reader a
merge a b = Reader $ do
    x <- combination a
    case x of
        Left x' -> return $ Left x'
        Right xio -> do
            y <- combination b
            case y of
                Left y' -> return $ Left y'
                Right yio -> return . Right $ do
                    rvar <- newEmptyMVar
                    xthr <- forkIO $ putMVar rvar =<< xio
                    ythr <- forkIO $ putMVar rvar =<< yio
                    result <- readMVar rvar
                    killThread xthr
                    killThread ythr
                    return result

nonblocking :: Reader a -> IO (Maybe a)
nonblocking r = do
    c <- combination r
    case c of
        Left x -> return $ Just x
        Right _ -> return Nothing

blocking :: Reader a -> IO a
blocking r = either return id =<< combination r

never :: Reader a
never = Reader . return . Right $ takeMVar =<< newEmptyMVar

-- A bit of a hack -- this doesn't belong in this module
-- Represents an IVar which is empty before the given time,
-- and full with the given value after it.  This *could*
-- be done using a thread that waits and then writes,
-- but it can be done more efficiently directly in terms
-- of the representation.
timed :: ClockTime -> a -> Reader a
timed t x = Reader $ do
    now <- getClockTime
    if now >= t
        then return $ Left x
        else return . Right $ do
            now' <- getClockTime
            let (TOD tsecs tpico, TOD nowsecs nowpico) = (t,now')
            let delaypico = 10^12 * (tsecs - nowsecs) + (tpico - nowpico)
            threadDelay . fromIntegral $ 1+(delaypico `div` 10^6)
            return x
