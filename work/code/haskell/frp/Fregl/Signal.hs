{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Signal
    ( Signal
    , SignalCell
    , readSignal
    , constSignal
    , cellSignal
    , newSignalCell
    , overwriteSignalCell
    , varSignal
    )
where


import Control.Monad
import Control.Applicative
import Control.Concurrent.STM
import Fregl.Vector

data SignalTag
    = TagEarly
    | TagLate
    deriving (Eq)

data Signal :: * -> * where
    SigConst :: a -> Signal a
    SigMap   :: (a -> b) -> Signal a -> Signal b
    SigApply :: Signal (a -> b) -> Signal a -> Signal b
    SigCell  :: SignalCell a -> Signal a
    SigVar   :: TVar a -> Signal a

newtype SignalCell a = SignalCell (TVar (Signal a, SignalTag))

readSignal :: Signal a -> STM a
readSignal = liftM fst . readSignal'
    where
    readSignal' :: Signal a -> STM (a, Maybe (Signal a))
    readSignal' (SigConst x) = return (x, Nothing)

    readSignal' (SigMap f siga) = do
        (v, repl) <- readSignal' siga
        return (f v, fmap (fmap f) repl)
    
    readSignal' (SigApply sigf siga) = do
        (f, replf) <- readSignal' sigf
        (a, repla) <- readSignal' siga
        let repl = case (replf, repla) of
                (Nothing, Nothing)     -> Nothing
                (Nothing, Just siga)   -> Just $ sigf <*> siga
                (Just sigf, Nothing)   -> Just $ sigf <*> siga
                (Just sigf, Just siga) -> Just $ sigf <*> siga
        return (f a, repl)
    
    readSignal' (SigCell (SignalCell cell)) = do
        (sig, tag) <- readTVar cell
        (v, repl) <- readSignal' sig
        case repl of
             Nothing -> return ()
             Just c -> writeTVar cell (c, tag)
        case tag of
             TagEarly -> return (v, Nothing)
             TagLate  -> return (v, Just sig)

    readSignal' (SigVar var) = do
        val <- readTVar var
        return (val, Nothing)

constSignal :: a -> Signal a
constSignal = SigConst

cellSignal :: SignalCell a -> Signal a
cellSignal = SigCell

varSignal :: TVar a -> Signal a
varSignal = SigVar

newSignalCell :: Signal a -> STM (SignalCell a)
newSignalCell a = SignalCell <$> newTVar (a, TagEarly)

overwriteSignalCell :: SignalCell a -> Signal a -> STM ()
overwriteSignalCell (SignalCell cell) a = do
    (_,tag) <- readTVar cell
    case tag of
         TagEarly -> writeTVar cell (a, TagLate)
         TagLate  -> fail "attempt to overwrite late signal"

instance Functor Signal where
    fmap f (SigConst a) = SigConst (f a)
    fmap f (SigMap f' s) = SigMap (f . f') s
    fmap f s = SigMap f s

instance Applicative Signal where
    pure = SigConst
    (<*>) = SigApply
