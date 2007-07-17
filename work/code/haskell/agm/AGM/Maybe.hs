{-# OPTIONS_GHC -fglasgow-exts #-}

-- From http://www.haskell.org/haskellwiki/New_monads/MaybeT

module AGM.Maybe
  (MaybeT(runMaybeT),
   module Control.Monad,
   module Control.Monad.Trans)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.State

newtype MaybeT m a = MaybeT {runMaybeT :: m (Maybe a)}

instance Functor m => Functor (MaybeT m) where
  fmap f x = MaybeT $ fmap (fmap f) $ runMaybeT x

instance Monad m => Monad (MaybeT m) where
  return = MaybeT . return . return
  x >>= f = MaybeT $ runMaybeT x >>= maybe (return Nothing) (runMaybeT . f)
  fail _ = MaybeT $ return Nothing

instance Monad m => MonadPlus (MaybeT m) where
  mzero = MaybeT $ return mzero
  mplus x y = MaybeT $ liftM2 mplus (runMaybeT x) (runMaybeT y)

-- Provide other MTL instances, for convenience

instance MonadTrans MaybeT where
  lift = MaybeT . liftM return


-- (Add other MTL instances, and a MonadFix instance)
