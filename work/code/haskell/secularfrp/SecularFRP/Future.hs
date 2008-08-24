module SecularFRP.Future 
    ( Time, DTime, Future
    , exact
    , order
    )
where

import Control.Monad (ap, MonadPlus)
import Control.Applicative

type Time = Double
type DTime = Double

class (Functor f, Applicative f, Monad f, MonadPlus f) 
        => Future f where
    exact :: Time -> a -> f a
    order :: f a -> f a -> f (a, f a)
