module Wait 
    ( DTime, Wait(..) )
where

import Control.Applicative
import Control.Arrow hiding (pure)
import Control.Monad
import Data.Monoid

type DTime = Double

newtype Wait a = Wait { runWait :: DTime -> Either (DTime,a) (Wait a) }

eitherF :: (a -> c) -> (b -> d) -> Either a b -> Either c d
eitherF f g = either (Left . f) (Right . g)

conj f = Wait . f . runWait

instance Functor Wait where
    fmap f = conj $ fmap (eitherF (second f) (fmap f))

instance Monad Wait where
    return x = Wait (const (Left (0,x)))
    w >>= f = Wait $ \dt ->
        case runWait w dt of
            Left (dt',x) -> runWait (adjust dt' (f x)) dt
            Right w' -> Right (w' >>= f)

instance Applicative Wait where
    pure = return
    (<*>) = ap

adjust :: DTime -> Wait a -> Wait a
adjust shift w = Wait $ \dt ->
    case runWait w (dt-shift) of
        Left (dt',x) -> Left (dt'+shift,x)
        Right w' -> Right w'

instance Monoid (Wait a) where
    mempty = Wait (const (Right mempty))
    mappend wa wb = Wait $ \dt -> 
        case runWait wa dt of
            Left (dta,a) -> 
                case runWait wb dta of
                    Left (dtb,b) -> Left (dtb,b)
                    Right _ -> Left (dta,a)
            Right wa' ->
                case runWait wb dt of
                    Left (dtb,b) -> Left (dtb,b)
                    Right wb' -> runWait (mappend wa' wb') dt
