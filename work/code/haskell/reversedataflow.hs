import Control.Applicative
import Control.Arrow hiding (pure)
import Control.Monad.Fix
import Control.Comonad
import Control.Monad
import Control.Monad.Trans
import Data.List

infixr 9 :<
data Stream a = a :< Stream a

sHead (a :< _) = a
sTail (_ :< as) = as
sDrop 0 s = s
sDrop n (a :< as) = sDrop (n-1) as

instance (Show a) => Show (Stream a) where
    show (a :< b :< c :< d :< e :< _) = intercalate " :< " (map show [a,b,c,d,e] ++ ["..."])

instance Functor Stream where
    fmap f (a :< as) = f a :< fmap f as

instance Monad Stream where
    return x = let r = x :< r in r
    m >>= f = joinS (fmap f m)

instance MonadFix Stream where
    mfix f = fix (sHead . f) :< mfix (sTail . f)

joinS ((x :< _) :< xss) = x :< joinS (fmap sTail xss)


newtype RStateT s m a = RStateT { runRStateT :: s -> m (s,a) }

instance (Functor m) => Functor (RStateT s m) where
    fmap f (RStateT r) = RStateT ((fmap.fmap.fmap) f r)

instance (MonadFix m) => Monad (RStateT s m) where
    return x = RStateT $ \s -> return (s,x)
    m >>= f = RStateT $ \s2 -> mdo
        ~(s1,b) <- runRStateT (f a) s2
        ~(s0,a) <- runRStateT m s1
        return (s0,b)

instance (MonadFix m) => MonadFix (RStateT s m) where
    mfix f = RStateT $ \s -> mdo
        ~(s',x) <- runRStateT (f x) s
        return (s',x)

instance MonadTrans (RStateT s) where
    lift m = RStateT $ \s -> liftM ((,) s) m


newtype DF a = DF { runDF :: RStateT Int Stream a }
    deriving (Functor, Monad, MonadFix)
newtype Var a = Var (Stream a)

computeDF df = fmap snd $ runRStateT (runDF df) 0

sample :: Var a -> DF a
sample (Var s) = DF . RStateT $ \d ->
    fmap ((,) d) (sDrop d s)

delay :: Int -> DF ()
delay n = DF . RStateT $ \d -> return (d+n,())

mainP av bv = mdo
    a <- sample av
    delay b
    b <- sample bv
    return (a,b)

nats :: Var Int
nats = Var $ let n x = x :< n (x+1) in n 0
