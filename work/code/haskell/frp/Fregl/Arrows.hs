{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Arrows 
    ( SP, runSP, sigSP, fromSP
    , SF, runSF, sf, sf_, sigSF, fromSF
    ) 
where

import Fregl.Signal
import Fregl.Event

import Control.Monad.Fix
import Control.Applicative
import Control.Arrow hiding (pure)

-- arrow for pointwise application of an arrow over signals
newtype SP a b c = SP { runSP :: Signal (a b c) }

instance (Arrow a) => Arrow (SP a) where
    arr     = SP . pure . arr
    first   = SP . fmap first . runSP
    f >>> g = SP (liftA2 (>>>) (runSP f) (runSP g))

instance (ArrowLoop a) => ArrowLoop (SP a) where
    loop = SP . fmap loop . runSP

instance (ArrowChoice a) => ArrowChoice (SP a) where
    left = SP . fmap left . runSP

sigSP :: (Arrow a) => Signal c -> SP a () c
sigSP sig = SP $ liftA arr $ const <$> sig

fromSP :: SP (->) () c -> Signal c
fromSP sp = runSP sp <*> pure ()


-- arrow for unrestricted signal composition
-- (like AFRP, but we also have the rest of Fregl :-)
newtype SF v b c = SF { runSF :: Signal b -> Event v (Signal c) }

instance Arrow (SF v) where
    arr f   = SF $ return . fmap f
    first f = SF $ \sigbd -> do
        sigc <- runSF f (fmap fst sigbd)
        return $ liftA2 (,) sigc (fmap snd sigbd)
    f >>> g = SF $ \sigb -> runSF f sigb >>= runSF g

instance ArrowLoop (SF v) where
    loop f = SF $ \sigb -> mdo
        sigcd <- runSF f sigbd
        let sigbd = liftA2 (,) sigb (fmap snd sigcd)
        return (fmap fst sigcd)

instance ArrowApply (SF v) where
    app = SF $ \sigabb -> do
        arrow <- readSig $ fmap fst sigabb
        runSF arrow (fmap snd sigabb)

sf :: (Signal b -> Event v (Signal c)) -> SF v b c
sf = SF

sf_ :: Event v (Signal c) -> SF v () c
sf_ = SF . const

sigSF :: Signal c -> SF v () c
sigSF sig = SF $ const (return sig)

fromSF :: SF v () c -> Event v (Signal c)
fromSF f = runSF f (pure ())
