{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

module Quantum
    (
    )
where

import Control.Arrow
import Data.Complex
import System.Random

type Amp = Complex Double
type StateVec a = [(a,Amp)]
type Observer = forall a b. (a -> IO b) -> Operator a b

data Operator b c 
    = Op (forall d. StateVec (b,d) -> IO (StateVec (c,d)))

data Quantum b c
    = Q (forall d. Operator (Either b d) (Either c d))

instance Arrow Operator where
    arr f             = 
        Op (return . map (\ ((st,d),p) -> ((f st,d),p)))
    (Op f) >>> (Op g) = 
        Op (\sts -> f sts >>= g)
    first (Op f)      = Op (\sts ->
        return . map (\ ((c,(k,d)),p) -> (((c,k),d),p))
        =<< f (map (\ (((b,k),d),p) -> ((b,(k,d)),p)) sts))


instance ArrowChoice Operator

instance Arrow Quantum where
    arr f           = Q (left (arr f))
    (Q f) >>> (Q g) = Q (f >>> g)
    first (Q f)     = Q (eitherToTuple ^>> first f >>^ tupleToEither)


instance ArrowChoice Quantum where
    left (Q f) = Q $ proc x -> do
        case x of
            Left (Left a)  -> f -< (Left a)
            Left (Right a) -> f -< (Right (Left a))
            Right a        -> f -< (Right (Right a))


first f :: (Either b d, e) -> (Either c d, e)
want :: (Either (b,e) d) -> (Either (c,e) d)


tupleToEither :: (Either a b, c) -> Either (a,c) (b,c)
tupleToEither (Left x,  y) = Left  (x,y)
tupleToEither (Right x, y) = Right (x,y)

eitherToTuple :: Either (a,c) (b,c) -> (Either a b, c)
eitherToTuple (Left  (x,y)) = (Left  x, y)
eitherToTuple (Right (x,y)) = (Right x, y)

trivial :: a
trivial = error "trivial"

observeWith :: (a -> a -> Bool) -> Operator a a
observeWith = trivial

