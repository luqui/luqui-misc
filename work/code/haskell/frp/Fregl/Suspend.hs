{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Suspend 
    ( MonadSuspend(..)
    , SuspendT, runSuspendT
    )
where

import Control.Monad
import Control.Monad.Trans

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
