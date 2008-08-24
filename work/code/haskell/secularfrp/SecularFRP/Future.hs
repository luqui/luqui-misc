module SecularFRP.Future 
    ( Time, DTime, Future
    , exact
    , orderFutures
    , pollFuture
    )
where

import Control.Monad (ap)
import Control.Applicative
import Data.Monoid

type Time = Double
type DTime = Double

data Future a
    = Exact Time a
    -- The first arg here gives a lower bound to when we know it's undefined
    | Unsure Time (DTime -> Future a)

exact :: Time -> a -> Future a
exact = Exact

infinity = 1/0 :: Time

instance Functor Future where
    fmap f (Exact t a) = Exact t (f a)
    fmap f (Unsure lb c) = Unsure lb (fmap f . c)

instance Monad Future where
    return = Exact (-infinity)
    m >>= f = joinFutures (fmap f m)

instance Applicative Future where
    pure = return
    (<*>) = ap

instance Monoid (Future a) where
    mempty = exact infinity (error "Value only defined at infinity. Wait a little longer.")
    mappend f g = fmap fst (orderFutures f g)

joinFutures :: Future (Future a) -> Future a
joinFutures (Exact t fut) = adjust t fut
joinFutures (Unsure lb c) = Unsure lb (joinFutures . c)

-- adjust t fut adjusts the occurrence time of fut to at least t
adjust t' (Exact t a) = Exact (max t t') a
adjust t' (Unsure lb f) = Unsure lb (adjust t' . f)

orderFutures :: Future a -> Future a -> Future (a, Future a)
orderFutures a@(Exact t x) b@(Exact t' x')
    | t <= t'   = Exact t (x, b)
    | otherwise = Exact t' (x', a)
orderFutures a@(Exact t x) b@(Unsure lb c)
    | t <= lb   = Exact t (x, b)
    | otherwise = Unsure lb (orderFutures a . c)
orderFutures a@(Unsure lb c) b@(Exact t x)
    | t <= lb   = Exact t (x, b)
    | otherwise = Unsure lb (orderFutures b . c)
orderFutures a@(Unsure lb c) b@(Unsure lb' c')
    = Unsure (min lb lb') (\dt -> orderFutures (c dt) (c' dt))


pollFuture :: Time -> Future a -> Either a (Future a)
pollFuture t' (Exact t a)   | t' >= t = Left a
pollFuture t' (Unsure lb c) | t' > lb = pollFuture t' (c (t' - lb))
pollFuture t' fut = Right fut
