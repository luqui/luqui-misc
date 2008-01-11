{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Suspend 
    ( MonadSuspend(..)
    , SuspendT, runSuspendT
    , mergeL
    )
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Fix

class (Monad m) => MonadSuspend v m | m -> v where
    attempt :: m a -> m (Either a (v -> m a))
    suspend :: m v

newtype SuspendT v m a 
    = SuspendT { runSuspendT :: m (Either a (v -> SuspendT v m a)) }

instance (Monad m) => Functor (SuspendT v m) where
    fmap = liftM

instance (Monad m) => Monad (SuspendT v m) where
    return x = SuspendT $ return $ Left x
    m >>= k  = SuspendT $ do
        choice <- runSuspendT m
        case choice of
             Left a  -> runSuspendT $ k a
             Right cont -> return $ Right $ \v -> cont v >>= k

instance MonadTrans (SuspendT v) where
    lift = SuspendT . liftM Left

instance (Monad m) => MonadSuspend v (SuspendT v m) where
    attempt = lift . runSuspendT
    suspend = SuspendT $ return $ Right return

instance (MonadIO m) => MonadIO (SuspendT v m) where
    liftIO = lift . liftIO

-- This is only a partial instance; it only works when
-- the given monad does not suspend.
--  (is it possible to make it work if it does?)
instance (MonadFix m) => MonadFix (SuspendT v m) where
    mfix f = SuspendT $ mfix (runSuspendT . f . fromLeft)
        where
        fromLeft (Left x) = x
        fromLeft _ = error "Monad suspended in mfix (not allowed)"

mergeL :: (MonadSuspend v m) => m a -> m a -> m a
mergeL mx my = do
    x <- attempt mx
    case x of
         Left  x' -> return x'
         Right contx -> do
             y <- attempt my
             case y of
                  Left y' -> return y'
                  Right conty -> do
                      v <- suspend
                      mergeL (contx v) (conty v)

