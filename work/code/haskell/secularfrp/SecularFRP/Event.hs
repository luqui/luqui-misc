module SecularFRP.Event 
    ( Event, iterateEvent, unsafeRunEvent )
where

import Control.Arrow ((***))
import Control.Monad (ap)
import Control.Applicative
import Data.Monoid
import SecularFRP.Future

newtype Event a = Event { runEvent :: Future (a, Event a) }

instance Functor Event where
    fmap f (Event fut) = Event (fmap (f *** fmap f) fut)

instance Monad Event where
    return x = Event (return (x, mempty))
    m >>= f = joinEvent (fmap f m)

instance Applicative Event where
    pure = return
    (<*>) = ap

instance Monoid (Event a) where
    mempty = Event mempty
    mappend (Event f) (Event f') = Event $ do
        ((x,ex), rest) <- orderFutures f f'
        return (x, ex `mappend` Event rest)

joinEvent :: Event (Event a) -> Event a
joinEvent fut = Event $ do
    (a,ee) <- runEvent fut
    runEvent $ a `mappend` joinEvent ee

iterateEvent :: a -> Event (a -> a) -> Event a
iterateEvent iv = Event . fmap next . runEvent
    where
    next (f,e') = let new = f iv in (new, iterateEvent new e')

unsafeRunEvent :: Event a -> Future (a, Event a)
unsafeRunEvent = runEvent
