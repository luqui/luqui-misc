import Prelude hiding (until)
import Control.Applicative
import Data.IORef
import Data.Monoid
import Control.Arrow hiding (pure)

type Time = Double

data Monotoney a
    = Monotoney { mAsk   :: Time -> IO (a, Monotoney a)
                , mClone :: IO (Monotoney a)
                }

instance Functor Monotoney where
    fmap f (Monotoney ask clone) = 
        Monotoney ((fmap.fmap) (f *** fmap f) ask) ((fmap.fmap) f clone)

instance Applicative Monotoney where
    pure x = let r = Monotoney (const (return (x,r))) (return r) in r
    f <*> x = Monotoney { mAsk   = \t -> do {
                                      (fv,monf) <- mAsk f t;
                                      (xv,monx) <- mAsk x t;
                                      return (fv xv, monf <*> monx)
                                   }
                        , mClone = liftA2 (<*>) (mClone f) (mClone x)
                        }

instance Monad Monotoney where
    return = pure
    m >>= f = 
        Monotoney { 
            mAsk = \t -> do {
                (a,m') <- mAsk m t;
                b <- mClone (f a);
                (b, _) <- mAsk b t;
                return (b, m' >>= f)      -- good time for a cache?  or leave it explicit?
            },
            mClone = do {
                m' <- mClone m;
                return $ m' >>= f
            }
        }

