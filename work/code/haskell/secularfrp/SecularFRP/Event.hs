module SecularFRP.Event 
    ( Event, iterateEvent, unsafeRunEvent )
where

import Control.Arrow ((***))
import Control.Monad (ap, MonadPlus(..))
import Control.Applicative
import Data.Monoid
import SecularFRP.Future

newtype Event f a = Event { runEvent :: f (a, Event f a) }

instance (Future f) => Functor (Event f) where
    fmap f (Event fut) = Event (fmap (f *** fmap f) fut)

instance (Future f) => Monad (Event f) where
    return x = Event (return (x, mempty))
    m >>= f = joinEvent (fmap f m)

instance (Future f) => Applicative (Event f) where
    pure = return
    (<*>) = ap

instance (Future f) => MonadPlus (Event f) where
    mzero = mempty
    mplus = mappend

instance (Future f) => Monoid (Event f a) where
    mempty = Event mzero
    mappend (Event f) (Event f') = Event $ do
        ((x,ex), rest) <- order f f'
        return (x, ex `mplus` Event rest)

joinEvent :: (Future f) => Event f (Event f a) -> Event f a
joinEvent fut = Event $ do
    (a,ee) <- runEvent fut
    runEvent $ a `mappend` joinEvent ee

iterateEvent :: (Future f) => a -> Event f (a -> a) -> Event f a
iterateEvent iv = Event . fmap next . runEvent
    where
    next (f,e') = let new = f iv in (new, iterateEvent new e')

unsafeRunEvent :: Event f a -> f (a, Event f a)
unsafeRunEvent = runEvent
