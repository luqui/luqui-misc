{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

module ComonadCore where

import Control.Arrow
import Control.Monad.Fix

class (Functor w) => Comonad w where
    pull   :: w a -> a
    (=>>)  :: w a -> (w a -> b) -> w b
    cojoin :: w a -> w (w a)
    cojoin w = w =>> id
    w =>> f  = fmap f (cojoin w)

type Time = Double
data Signal a = Signal a (Time -> Signal a)

instance Functor Signal where
    fmap f (Signal a trans) = Signal (f a) (fmap f . trans)

instance Comonad Signal where
    pull (Signal a _) = a
    cojoin sig@(Signal _ trans) = Signal sig (cojoin . trans)

zipSignal :: Signal a -> Signal b -> Signal (a,b)
zipSignal (Signal a transa) (Signal b transb) =
    Signal (a,b) $ \dt -> zipSignal (transa dt) (transb dt)

newtype SF b c = SF { runSF :: forall d. Signal (b,d) -> IO (Signal (c,d)) }

instance Arrow SF where
    arr f = SF $ return . fmap (first f)
    f >>> g = SF $ \x -> runSF f x >>= runSF g
    first f = SF $ 
        fmap (fmap shuffleLeft) . runSF f . fmap shuffleRight

instance ArrowLoop SF where
    loop f = SF $ \sigb -> mdo
        sigcd <- runSF f sigbd
        -- hmm, do we use sigb's dummy, or sigcd's?  I think there's a right answer.
        sigbd <- return $ fmap shuffleLeft (fmap fst sigb `zipSignal` fmap (first snd) sigcd)
        return $ fmap (first fst) sigcd


shuffleLeft (a,(b,c)) = ((a,b),c)
shuffleRight ((a,b),c) = (a,(b,c))
