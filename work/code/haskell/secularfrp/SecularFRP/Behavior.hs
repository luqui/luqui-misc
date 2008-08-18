module SecularFRP.Behavior where

import Control.Arrow (second)
import Control.Applicative
import SecularFRP.Event
import SecularFRP.Stream
import Data.Monoid
import Control.Compose

data ReactiveF i a = a `Stepper` EventF i a

instance Functor (ReactiveF i) where
    fmap f (x `Stepper` xs) = f x `Stepper` fmap f xs

combine :: a -> b -> EventF i (Either a b) -> EventF i (a,b)
combine a0 b0 = EventF . scan go (undefined,(a0,b0)) . runEventF
    where
    go (_,(a,b)) (t,v) =
        case v of
             Left a'  -> (t,(a',b))
             Right b' -> (t,(a,b'))

instance Applicative (ReactiveF i) where
    pure x = x `Stepper` mempty
    (f `Stepper` fs) <*> (x `Stepper` xs) = 
        f x `Stepper` 
            fmap (uncurry ($)) (combine f x (merge (fmap Left fs) (fmap Right xs)))


data Fun a = Fun (DTime -> a)
           | K a

instance Functor Fun where
    fmap f (Fun t) = Fun (f . t)
    fmap f (K x)   = K (f x)

instance Applicative Fun where
    pure = K
    Fun tf <*> Fun xf  = Fun (tf <*> xf)
    Fun tf <*> K x     = Fun (\i -> tf i x)
    K t    <*> Fun xf  = Fun (\i -> t (xf i))
    K t    <*> K x     = K (t x)

type BehaviorF i = ReactiveF i :. Fun
