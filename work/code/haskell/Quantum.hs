{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

module Quantum
    ( Quantum
    , entangle
    , qIO
    , qIO_
    , qCheatInspect
    , runQuantum
    )
where

import Control.Arrow
import Data.Complex
import System.Random
import Debug.Trace

type Amp = Complex Double
type StateVec a = [(a,Amp)]

data Operator b c 
    = Op (forall d. StateVec (b,d) -> IO (StateVec (c,d)))

instance Arrow Operator where
    arr f             = 
        Op (return . map (\ ((st,d),p) -> ((f st,d),p)))
    (Op f) >>> (Op g) = 
        Op (\sts -> f sts >>= g)
    first (Op f)      = Op (\sts ->
        return . map (\ ((c,(k,d)),p) -> (((c,k),d),p))
        =<< f (map (\ (((b,k),d),p) -> ((b,(k,d)),p)) sts))

instance ArrowChoice Operator where
    left (Op f) = Op (\sts -> do
        let lefts  = [ ((st,d),p) | ((Left  st,d),p) <- sts ]
        let rights = [ ((st,d),p) | ((Right st,d),p) <- sts ]
        lefts' <- f lefts
        return $ [ ((Left  st,d),p) | ((st,d),p) <- lefts' ]
              ++ [ ((Right st,d),p) | ((st,d),p) <- rights ])

opObserveWith :: forall a. (a -> a -> Bool) -> Operator a a
opObserveWith eq = Op $ \sts -> do
    pick $ classify eq sts

classify :: (a -> a -> Bool) -> StateVec (a,b) -> StateVec (a, StateVec (a,b))
classify eq = classify' []
    where
    classify' accum [] = accum
    classify' accum (((a,b),p):xs) = 
        case break (\ ((a',_),_) -> eq a a') accum of
            (pre,[]) -> 
                classify' (((a,[((a,b),p)]),p):pre) xs
            (pre,(((_,bs),p'):posts)) ->
                classify' (pre ++ ((a,((a,b),p):bs),p+p'):posts) xs

pick :: StateVec (a, StateVec (a,b)) -> IO (StateVec (a,b))
pick []  = return []
pick sts = pick' 0 undefined sts

pick' accum cur [] = return (snd cur)
pick' accum cur (((a,bs),p):xs) = do
    let prob = magnitude p^2
    rand <- randomRIO (0, accum + prob)
    pick' (accum + prob) 
          (if rand <= prob then (a,bs) else cur)
          xs

    

opEntangle :: Operator [(a,Amp)] a
opEntangle = 
    Op (\sts -> return [ ((a,d),p*p') | ((st,d),p) <- sts, (a,p') <- st ])
    
opIO :: (Eq a) => (a -> IO b) -> Operator a b
opIO f = opObserveWith (==) >>> Op (\sts -> do
    case sts of
        (((b,_),_):_) -> do
            result <- f b
            return [ ((result,d),p) | ((_,d),p) <- sts ]
        [] -> return [])

opCheatInspect :: (Eq b, Show b) => Operator b ()
opCheatInspect = Op $ \sts -> do
    print [ (st,p) | ((st,_),p) <- classify (==) sts ]
    return [ (((),d),p) | ((st,d),p) <- sts ]
    
runOperator :: Operator a b -> [(a,Amp)] -> IO [(b,Amp)]
runOperator (Op f) sts = do
    ret <- f [ ((st,()),p) | (st,p) <- sts ]
    return [ (st,p) | ((st,_),p) <- ret ]



data Quantum b c
    = Q (forall d. Operator (Either b d) (Either c d))

instance Arrow Quantum where
    arr f           = Q (left (arr f))
    (Q f) >>> (Q g) = Q (f >>> g)
    first (Q f)     = Q (eitherToTuple ^>> first f >>^ tupleToEither)

instance ArrowChoice Quantum where
    left (Q f) = Q (shuffleRightEither ^>> f >>^ shuffleLeftEither)

observeBranch :: Quantum a a
observeBranch = Q (opObserveWith sameSide)

entangle :: Quantum [(a,Amp)] a
entangle = Q (left opEntangle)

qIO :: (Eq a, Show a) => (a -> IO b) -> Quantum a b
qIO f = observeBranch >>> Q (left (opIO f))

qIO_ :: IO b -> Quantum () b
qIO_ = qIO . const

runQuantum :: Quantum a b -> [(a,Amp)] -> IO [(b,Amp)]
runQuantum (Q q) = runOperator (Left ^>> q >>^ either id undefined)

qCheatInspect :: (Eq b, Show b) => Quantum b ()
qCheatInspect = Q (left opCheatInspect)


sameSide :: Either a b -> Either c d -> Bool
sameSide (Left _)  (Left _)  = True
sameSide (Right _) (Right _) = True
sameSide _          _        = False

shuffleRightEither :: Either (Either a b) c -> Either a (Either b c)
shuffleRightEither = either (either Left (Right . Left)) (Right . Right)

shuffleLeftEither :: Either a (Either b c) -> Either (Either a b) c
shuffleLeftEither = either (Left . Left) (either (Left . Right) Right)

tupleToEither :: (Either a b, Either c ()) -> Either (a,c) b
tupleToEither (Left x, Left y)    = Left (x,y)
tupleToEither (Right x, Right ()) = Right x
tupleToEither _                   = error "Non-homogeneous pair"

eitherToTuple :: Either (a,b) c -> (Either a c, Either b ())
eitherToTuple (Left  (x,y)) = (Left x, Left y)
eitherToTuple (Right x)     = (Right x, Right ())

