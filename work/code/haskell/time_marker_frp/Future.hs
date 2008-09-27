{-# LANGUAGE BangPatterns #-}

module Future 
    ( (:<), GLB
    , LowerBound, GreatestLowerBound
    , transitive, reflexive, isglb
    , Time, Future, After
    , project, deduce, wait, first, callback
    )
where

import Control.Applicative
import Control.Monad (liftM2)
import System.IO.Unsafe (unsafePerformIO, unsafeInterleaveIO)
import Control.Concurrent
import System.Posix.Time

data t :< t' = FakeLT
data GLB t t' = FakeGLB

type LowerBound a b inf = (inf :< a, inf :< b)
type GreatestLowerBound a b inf = (LowerBound a b inf, forall i. LowerBound a b i -> i :< inf)

transitive :: (a :< b) -> (b :< c) -> (a :< c)
transitive !a !b = FakeLT

reflexive  :: a :< a
reflexive = FakeLT

isglb :: GreatestLowerBound t t' (GLB t t')
isglb = ((FakeLT, FakeLT), \x -> x `seq` FakeLT)

data Time = Any | Finite Double
data Future t a = Future { fCheck :: IO Bool, fTime :: Time, fVal :: a }

instance Functor (Future t) where
    fmap f fut = Future { fCheck = fCheck fut, fTime = fTime fut, fVal = f (fVal fut) }

instance Applicative (Future t) where
    pure = Future (return True) Any
    f <*> x
        = Future (fCheck x <&&> fCheck f) time (fVal f (fVal x))
            where
            time = mergeTime (fTime f) (fTime x)

instance Monad (Future t) where
    return = pure
    m >>= f = 
        Future (fCheck m <&&> fCheck result) 
               (mergeTime (fTime m) (fTime result))
               (fVal result)
        where
        result = f (fVal m)

a <&&> b = do
    a' <- a
    if a' then b else return False

a <||> b = do
    a' <- a
    if a' then return True else b

newtype After t' = After (forall t a. t :< t' -> Future t a -> a)

project :: After t' -> t :< t' -> Future t a -> a
project (After f) = f

deduce :: Future t' (After t')
deduce = pure after

wait :: Future t a -> IO (a, After t)
wait (Future check time a) = do
    return $! a
    return (a, after)

first :: Future t a -> Future t' b -> Future (GLB t t') (Either (a, t :< GLB t t') (b, t' :< GLB t t'))
first fa fb = Future (fCheck fa <||> fCheck fb) (fTime result) (fVal result)
    where
    aret = Future (return True) (fTime fa) (Left (fVal fa, FakeLT))
    bret = Future (return True) (fTime fb) (Right (fVal fb, FakeLT))
    result = unsafePerformIO $ do
        aready <- fCheck fa
        if not aready then return bret else do
        bready <- fCheck fb
        if not bready then return aret else do
        return $ case (fTime fa, fTime fb) of
                        (Any,_)        -> aret
                        (Finite _,Any) -> bret
                        (Finite t, Finite u) | t <= u    -> aret
                                             | otherwise -> bret

after :: After t
after = After $ \cmp (Future _ _ x) -> cmp `seq` x

callback :: (forall t. IO (a -> IO (After t), Future t a) -> r) -> r
callback f = f ret 
    where 
    ret = do
        v <- newEmptyMVar
        r <- unsafeInterleaveIO (readMVar v)
        let sink a = do
                t <- now
                putMVar v (t, a)
                return after
        let fut = Future (isEmptyMVar v) (Finite (fst r)) (snd r)
        return (sink, fut)
    
now :: IO Double
now = realToFrac <$> epochTime
    

mergeTime a b = 
    case (a, b) of
       (Finite x, Any)               -> Finite x
       (Any, Finite x)               -> Finite x
       (Finite x, Finite y) | x == y -> Finite x
       (Any, Any)                    -> Any
