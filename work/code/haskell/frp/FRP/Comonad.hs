module FRP.Comonad 
    ( Comonad(..)
    , Cokleisli(..)
    )
where

import Control.Arrow

class (Functor w) => Comonad w where
    pull     :: w a -> a
    cojoin   :: w a -> w (w a)
    (=>>)    :: w a -> (w a -> b) -> w b
    cojoin w = w =>> id
    w =>> f  = fmap f (cojoin w)

newtype Cokleisli w a b = Cokleisli { runCokleisli :: w a -> b }

instance (Comonad w) => Arrow (Cokleisli w) where
    arr f = Cokleisli (f . pull)
    (Cokleisli f) >>> (Cokleisli g) = Cokleisli (\w -> g (w =>> f))
    first (Cokleisli f) = Cokleisli (\w -> 
        (f (fmap fst w), snd (pull w)))

-- Is this valid?
instance (Comonad w) => ArrowApply (Cokleisli w) where
    app = Cokleisli $ \w ->
        runCokleisli (fst (pull w)) $ fmap snd w

instance (Comonad w) => ArrowChoice (Cokleisli w) where
    left = leftApp
