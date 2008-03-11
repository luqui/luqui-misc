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

-- |Representation of a probability amplitude
type Amp = Complex Double

-- |An eigenstate, qsAmp |qsValue>
data QState a = QState { qsValue :: a, qsAmp :: Amp }

-- |A quantum state: a sum of eigenstates (represented as a list)
type QStateVec a = [QState a]

-- |QState is a functor that maps the value and keeps the
-- probability amplitude fixed.
instance Functor QState where
    fmap f (QState x p) = QState (f x) p

-- |The Operator arrow is half of a Quantum arrow: it represents
-- the "parallel" nature of quantum computations, but only handles
-- choice in a "pure" way; that is, if you have:
--
-- > if x > 0
-- >     then opIO print -< "Hello"
-- >     else opIO print -< "Goodbye"
--
-- Then if x represents a superposition of both positive and
-- negative numbers, both "Hello" and "Goodbye" will be printed
-- (x taking on positive values in the then branch and negative
-- values in the else branch).  This is leveraged by the Quantum
-- arrow to do proper branch collapsation.
--
-- It is implemented as a function from quantum states to quantum
-- states (plus IO to do, well, I/O).  But the states are augmented
-- by a dummy parameter 'd' to keep track of the relationship between
-- the input and the output.  So if the value |1> generated the value
-- |"foo"> in the output, then we know that when we collapse the
-- input to 1, whatever the output of this computation was has to
-- be collapsed to "foo" simultaneously.  The dummy parameter
-- implements entanglement!
data Operator b c 
    = Op (forall d. QStateVec (b,d) -> IO (QStateVec (c,d)))

instance Arrow Operator where
    arr f             = 
        Op (return . mapStateVec f)
    (Op f) >>> (Op g) = 
        Op (\sts -> f sts >>= g)
    first (Op f)      = 
        Op (fmap (map (fmap shuffleLeftPair)) -- move it back
          . f 
          . map (fmap shuffleRightPair))      -- move the fixed argument to the dummy parameter

instance ArrowChoice Operator where
    left (Op f) = Op $ \sts -> do
        -- Our QStateVecs represent a sum, so the list is commutative.
        -- So let's just split up the input based on what we want
        -- f to transform and what we dont...
        let lefts  = [ QState (st,d) p | QState (Left  st,d) p <- sts ]
        let rights = [ QState (st,d) p | QState (Right st,d) p <- sts ]
        -- ...transform half of it...
        lefts' <- f lefts
        -- ...and merge them back together...
        return $ mapStateVec Left lefts'
              ++ mapStateVec Right rights

-- |opObserveWith f takes an equivalence relation f, splits the state 
-- space into equivalence classes based on f, and then randomly chooses
-- one based on the probablity sum of each class.  The output is
-- the chosen class.
opObserveWith :: (a -> a -> Bool) -> Operator a a
opObserveWith eq = Op $ \sts -> do
    let cls = classify eq sts
    if null cls
        then return []
        else fmap snd $ pick (classify eq sts)

-- |classify is a helper function for opObserveWith which splits the input into
-- equivalence classes, finding the sum of the amplitudes of the states in each
-- class (for selection purposes).  It returns a state vector of (a, QStateVec
-- (a,b)):  the first element of the tuple is an arbitrary representitave of the
-- class; the second element is the class itself (represented as a state vector).
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
        classify' sts

-- |pick is a helper function for opObserveWith which takes a state vector and
-- chooses an element from it at random based on the argument squared of the 
-- probability amplitudes.
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

    
-- |opEntangle is an Operator arrow which takes a list of eigenstates and 
-- amplitudes and constructs a state vector out of them. 
opEntangle :: Operator [(a,Amp)] a
opEntangle = Op $ \sts ->
    return [ QState (a,d) (p*p') 
             | QState (st,d) p <- sts
             , (a,p') <- st ]
    
-- |opIO takes an IO action and converts it into a quantum arrow.  The
-- arrow observes the input to the action, collapsing the state, before
-- performing the action.
opIO :: (Eq a) => (a -> IO b) -> Operator a b
opIO f = opObserveWith (==) >>> Op (\sts -> do
    case sts of
        (s:_) -> do
            result <- f $ fst $ qsValue s
            return [ QState (result,d) p | QState (_,d) p <- sts ]
        [] -> return [])

-- |opCheatInspect is an arrow which prints the state vector of the
-- value passed in to standard output.  Using this is like observing
-- a quantum state without measuring it, so if you use it, you should
-- feel dirty.
opCheatInspect :: (Eq b, Show b) => Operator b ()
opCheatInspect = Op $ \sts -> do
    print [ (st,p) | QState (st,_) p <- classify (==) sts ]
    return [ QState ((),d) p | QState (_,d) p <- sts ]
 
-- |runOperator takes an input state vector, runs it through the given
-- Operator arrow, and returns a state vector of outputs.
runOperator :: Operator a b -> [(a,Amp)] -> IO [(b,Amp)]
runOperator (Op f) sts = do
    ret <- f [ QState (st,()) p | (st,p) <- sts ]
    return [ (st,p) | QState (st,()) p <- ret ]


-- |The Quantum arrow represents a quantum computation with observation.
-- You can give a quantum computation a superposition of values, and
-- it will operate over them, returning you a superposition back.  If
-- ever you do I/O (using the qIO or qIO_ functions), the system
-- collapses to an eigenstate of what you did I/O on.
--
-- > x <- entangle -< [(1, 1 :+ 0), (2, 1 :+ 0)]
-- > -- x is in state |1> + |2>; i.e. 1 or 2 with equal probability
-- > let y = x + 1
-- > -- y is in state |2> + |3>
-- > qIO print -< y    -- will print either 2 or 3; let's say it printed 2
-- > -- state collapses here, y in state |2>
-- > qIO print -< x    -- prints 1 (assuming 2 was printed earlier)
--
-- So the variables become entangled with each other in order to
-- maintain consistency of the computation. 
data Quantum b c
    -- |It is implemented by a "choice" over the Operator arrow.
    -- The Left states represent values in the current "branch" 
    -- (think if statements, so eg. the "then" branch) computation,
    -- and the Right is states elsewhere.  If we decide to collapse,
    -- we need to collapse into a single branch.  If we chose the
    -- Left branch, we prune out all Right states from the input.
    -- If we chose the Right branch, we prune all Left states
    -- (thus "aborting" the current branch).
    = Q (forall d. Operator (Either b d) (Either c d))

instance Arrow Quantum where
    arr f           = Q (left (arr f))
    (Q f) >>> (Q g) = Q (f >>> g)
    first (Q f)     = Q (eitherToTuple ^>> first f >>^ tupleToEither)

instance ArrowChoice Quantum where
    left (Q f) = Q (shuffleRightEither ^>> f >>^ shuffleLeftEither)

-- |observeBranch forces the computation to collapse into a 
-- single branch:
--
-- > x <- entangle -< [(1, 1 :+ 0), (2, 1 :+ 0)]
-- > if x == 1
-- >     then do ...
-- >             observeBranch -- decide NOW whether x is 1 or not
-- >     else ...
--
-- This is /the/ function for which the two-stage Operator/Quantum
-- distinction was written, to be able to collapse conditionals
-- "after they happen" rather than "as they happen".
observeBranch :: Quantum a a
observeBranch = Q (opObserveWith sameSide)

-- |entangle takes as input a list of values and probability 
-- amplitudes and gives as output a superposition of the inputs.
-- For example:
--
-- > x <- entangle -< [(1, 1 :+ 0), (2, 0 :+ 1)]
-- > -- x is now |1> + i|2>
-- > qIO print -< x    -- prints 1 or 2 with equal probability
entangle :: Quantum [(a,Amp)] a
entangle = Q (left opEntangle)

-- |@qIO f -< x@ first collapses @x@ to an eigenstate (using observe) then
-- executes @f x@ in the IO monad.  All conditionals up to this point are 
-- collapsed to an eigenstate (True or False) so a "current branch" of 
-- the computation is selected.
qIO :: (Eq a) => (a -> IO b) -> Quantum a b
qIO f = observeBranch >>> Q (left (opIO f))

-- |qIO_ is just qIO which doesn't take an input.  eg.
--
-- > qIO_ $ print "hello world" -< ()
--
-- All conditionals up to this point are collapsed to an eigenstate 
-- (True or False) so a "current branch" of the computation is selected.
qIO_ :: IO b -> Quantum () b
qIO_ = qIO . const

-- |@observeWith f@ takes an equivalence relation f, breaks the state
-- space into eigenstates of that relation, and collapses to one.  
-- For example:
--
-- > x <- entangle -< map (\s -> (s,1 :+ 0)) [1..20]
-- > observeWith (\x y -> x `mod` 2 == y `mod` 2)
--
-- Will collapse @x@ to be either even or odd, but make no finer
-- decisions than that.
observeWith :: (a -> a -> Bool) -> Quantum a a
observeWith f = Q (left (opObserveWith f))

-- |observe is just observeWith on equality.
observe :: (Eq a) => Quantum a a
observe = observeWith (==)

-- |runQuantum takes an input state vector, runs it through the given
-- Quantum arrow, and returns a state vector of outputs.
runQuantum :: Quantum a b -> [(a,Amp)] -> IO [(b,Amp)]
runQuantum (Q q) = runOperator (Left ^>> q >>^ either id undefined)

-- |@execQuantum q x@ passes the state |x> through q, collapses q's
-- output to an eigenstate, and returns it.
execQuantum :: (Eq b) => Quantum a b -> a -> IO b
execQuantum q a = 
    fmap (fst . head) $ runQuantum (q >>> observeWith (==)) [(a, 1 :+ 0)]

-- |@cheatInspect x@ shows the current state of x as a linear
-- combination of its eigenstates.
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

