import Control.Applicative
import Control.Arrow hiding (pure)
import Control.Monad.Fix
import Control.Comonad
import Data.List

infixr 9 :<
data Stream a = a :< Stream a

sHead (a :< _) = a
sTail (_ :< as) = as

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
nats = 0 :< fmap succ nats


-- rstate, etc.
