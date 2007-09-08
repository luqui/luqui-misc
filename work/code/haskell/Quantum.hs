{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

module Quantum
    ( Quantum
    , entangle
    , qIO
    , qIO_
    , cheatInspect
    , observeWith
    , observe
    , runQuantum
    , execQuantum
    )
where

import Control.Arrow
import Data.Complex
import System.Random
import Control.Monad.State

type Amp = Complex Double
data QState a = QState { qsValue :: a, qsAmp :: Amp }
type QStateVec a = [QState a]

instance Functor QState where
    fmap f (QState x p) = QState (f x) p

data Operator b c 
    = Op (forall d. QStateVec (b,d) -> IO (QStateVec (c,d)))

instance Arrow Operator where
    arr f             = 
        Op (return . mapStateVec f)
    (Op f) >>> (Op g) = 
        Op (\sts -> f sts >>= g)
    first (Op f)      = 
        Op (fmap (map (fmap shuffleLeftPair)) 
          . f 
          . map (fmap shuffleRightPair))

instance ArrowChoice Operator where
    left (Op f) = Op $ \sts -> do
        let lefts  = [ QState (st,d) p | QState (Left  st,d) p <- sts ]
        let rights = [ QState (st,d) p | QState (Right st,d) p <- sts ]
        lefts' <- f lefts
        return $ mapStateVec Left lefts'
              ++ mapStateVec Right rights

opObserveWith :: (a -> a -> Bool) -> Operator a a
opObserveWith eq = Op $ \sts -> do
    let cls = classify eq sts
    if null cls
        then return []
        else fmap snd $ pick (classify eq sts)

classify :: (a -> a -> Bool) -> QStateVec (a,b) -> QStateVec (a, QStateVec (a,b))
classify eq xs = execState (classify' xs) []
    where
    classify' [] = return ()
    classify' (QState (a,b) p:sts) = do
        accum <- get
        case break (\(QState (a',_) _) -> eq a a') accum of
            (pre, []) -> do
                put $ QState (a, [QState (a,b) p]) p : pre
            (pre, QState (_,bs) p' : posts) ->
                put $ pre ++ QState (a, QState (a,b) p : bs) (p+p') : posts
        classify' xs

pick :: QStateVec a -> IO a
pick sts = pick' 0 (error "empty state") sts
    where
    pick' accum cur [] = return cur
    pick' accum cur (QState x p : xs) = do
        let prob = magnitude p^2
        rand <- randomRIO (0, accum + prob)
        pick' (accum + prob)
              (if rand <= prob then x else cur)
              xs

    

opEntangle :: Operator [(a,Amp)] a
opEntangle = 
    Op (\sts -> return [ QState (a,d) (p*p') 
                         | QState (st,d) p <- sts
                         , (a,p') <- st ])
    
opIO :: (Eq a) => (a -> IO b) -> Operator a b
opIO f = opObserveWith (==) >>> Op (\sts -> do
    case sts of
        (s:_) -> do
            result <- f $ fst $ qsValue s
            return [ QState (result,d) p | QState (_,d) p <- sts ]
        [] -> return [])

opCheatInspect :: (Eq b, Show b) => Operator b ()
opCheatInspect = Op $ \sts -> do
    print [ (st,p) | QState (st,_) p <- classify (==) sts ]
    return [ QState ((),d) p | QState (_,d) p <- sts ]
    
runOperator :: Operator a b -> [(a,Amp)] -> IO [(b,Amp)]
runOperator (Op f) sts = do
    ret <- f [ QState (st,()) p | (st,p) <- sts ]
    return [ (st,p) | QState (st,()) p <- ret ]



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

qIO :: (Eq a) => (a -> IO b) -> Quantum a b
qIO f = observeBranch >>> Q (left (opIO f))

qIO_ :: IO b -> Quantum () b
qIO_ = qIO . const

observeWith :: (a -> a -> Bool) -> Quantum a a
observeWith f = Q (left (opObserveWith f))

observe :: (Eq a) => Quantum a a
observe = observeWith (==)

runQuantum :: Quantum a b -> [(a,Amp)] -> IO [(b,Amp)]
runQuantum (Q q) = runOperator (Left ^>> q >>^ either id undefined)

execQuantum :: (Eq b) => Quantum a b -> a -> IO b
execQuantum q a = 
    fmap (fst . head) $ runQuantum (q >>> observeWith (==)) [(a, 1 :+ 0)]

cheatInspect :: (Eq b, Show b) => Quantum b ()
cheatInspect = Q (left opCheatInspect)


mapStateVec :: (a -> b) -> QStateVec (a,d) -> QStateVec (b,d)
mapStateVec = map . fmap . first

sameSide :: Either a b -> Either c d -> Bool
sameSide (Left _)  (Left _)  = True
sameSide (Right _) (Right _) = True
sameSide _          _        = False

shuffleRightPair :: ((a,b),c) -> (a,(b,c))
shuffleRightPair ((a,b),c) = (a,(b,c))

shuffleLeftPair :: (a,(b,c)) -> ((a,b),c)
shuffleLeftPair (a,(b,c)) = ((a,b),c)

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

