{-# LANGUAGE BangPatterns #-}

module Temporal.At where

import Control.Monad (ap)
import Control.Monad.Instances ()
import Control.Arrow (second)
import Control.Applicative
import Data.IORef

type TimeT = Double

-- an "object" which yields values of type a at a given time,
-- with the restriction that you may only ask in a monotone way.
-- The bool is a "constant" indicator; if it is true, then asking
-- again will always return the same value.  And yes it is most
-- hideous.
newtype At t a = At { runAt :: TimeT -> IO (Bool,a) }
conjAt f = At . f . runAt

instance Functor (At t) where
    fmap = conjAt . fmap . fmap . second

instance Applicative (At t) where
    pure = return 
    f <*> x = At $ \t -> do
        (fconst, fv) <- runAt f t
        (xconst, xv) <- runAt x t
        return (fconst && xconst, fv xv)

instance Monad (At t) where
    return = At . return . return . (,) True
    m >>= f = At $ \t -> do
        (aconst, a) <- runAt m t
        (bconst, b) <- runAt (f a) t
        return (aconst && bconst, b)


newtype Time t = Time TimeT

newtype Behavior t a = Behavior { runBehavior :: forall t'. t :< t' -> At t' a }

data t :< t' = FakeLT
    deriving Show

newtype Gen a = Gen (IO a)
    deriving (Functor, Applicative, Monad)

switch :: At t (Time t') -> At t (Either (t :< t') (t' :< t))
switch timem = At $ \t -> do
    (timeconst, Time time) <- runAt timem t
    if t < time then return (False, Left FakeLT) 
                else return (timeconst, Right FakeLT)

integral :: forall t. Behavior t Double -> At t (Behavior t Double)
integral beh = At $ \t -> do
    tracker <- newIORef (t,0)
    let follow = runBehavior beh FakeLT   -- OMG HAX!
    let ret = Behavior (\_ -> At $ \t' -> do
         let integrate samplet !accum
              | samplet >= t' = return (samplet,accum)
              | otherwise = do
                 (_,sample) <- runAt follow t'
                 integrate (samplet + stepSize) (accum + stepSize * sample)
         (curt, curv) <- readIORef tracker
         (newt, newv) <- integrate curt curv
         writeIORef tracker (newt,newv)
         return (False,newv))
    return (False,ret)
    where
    stepSize = 0.01  -- XXX
