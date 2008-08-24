module Control.Monad.Free (FreeT(..)) where

import Control.Applicative
import Control.Monad (liftM)
import Control.Monad.Trans

{- | @FreeT f@ is a monad transformer for free monads over a functor @f@. 
-}
newtype FreeT f m a = FreeT { runFreeT :: m (Either a (f (FreeT f m a))) }

editEither l r = either (Left . l) (Right . r)
conj f = FreeT . f . runFreeT

instance (Functor f, Functor m) => Functor (FreeT f m) where
    fmap f = conj $ fmap (editEither f ((fmap.fmap) f))

instance (Functor f, Monad m) => Monad (FreeT f m) where
    return = FreeT . return . Left
    m >>= f = FreeT $ do
        r <- runFreeT m
        case r of
             Left x   -> runFreeT $ f x
             Right xc -> return . Right $ fmap (>>= f) xc

instance (Functor f) => MonadTrans (FreeT f) where
    lift = FreeT . liftM Left
