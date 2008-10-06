module Temporal.DynAction 
    ( DynAction, mkDynAction, runDynAction
    , cacheST, liftDyn
    )
where

import Control.Arrow hiding (pure)
import Control.Monad.ST.Lazy
import Data.STRef.Lazy
import Data.IORef

newtype DynAction m a b = DynAction { runDynAction :: a -> m (b, DynAction m a b) }

-- In mkDynAction f, there is the following proof obligation:
--    f = \x -> do { (b,_) <- f x ; return (b, mkDynAction f) }
mkDynAction :: (Monad m) => (a -> m (b, DynAction m a b)) -> DynAction m a b
mkDynAction = DynAction

instance (Functor m) => Functor (DynAction m a) where
    fmap f (DynAction a) = DynAction (fmap (fmap (f *** fmap f)) a)

instance (Monad m) => Arrow (DynAction m) where
    arr f = let r = DynAction $ \a -> return (f a, r) in r
    DynAction f >>> DynAction g = DynAction $ \a -> do
        ~(b,f') <- f a
        ~(c,g') <- g b
        return (c, f' >>> g')
    first (DynAction f) = DynAction $ \(~(a,c)) -> do
        ~(b,f') <- f a
        return ((b,c), first f')

instance (Monad m) => ArrowChoice (DynAction m) where
    left (DynAction f) = r where 
        r = DynAction $ \eac -> 
            case eac of
                Left a -> do
                    ~(b,f') <- f a
                    return (Left b, left f')
                Right c -> return (Right c, r)

instance (Monad m) => ArrowApply (DynAction m) where
    app = DynAction $ \(~(sub,a)) -> do
              ~(b,_) <- runDynAction sub a  -- forgets the optimization.  use cache to remember it.
              return (b, app)


cacheST :: DynAction (ST s) a b -> ST s (DynAction (ST s) a b)
cacheST action = do
        ref <- newSTRef action
        let r = DynAction $ \a -> do
                    cur <- readSTRef ref
                    ~(b,new) <- runDynAction cur a
                    writeSTRef ref new
                    return (b,r)
        return r

liftDyn :: (Monad m) => (a -> m b) -> DynAction m a b
liftDyn f = r where
    r = DynAction $ \a -> do
            b <- f a
            return (b,r)


