{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

module Fregl.Core 
    ( integral
    , when
    , delay
    , time
    , loadImage
    , module Graphics.UI.SDL.Keysym
    )
where

import Fregl.Signal
import Fregl.Event
import Fregl.Vector
import qualified Fregl.Drawing as Draw
import Control.Concurrent.STM
import Control.Applicative
import Debug.Trace
import Graphics.UI.SDL.Keysym


-- standard combinators

integral :: (Vector v, Field v ~ Double) 
         => v -> Signal v -> Event (Signal v)
integral init sig = pure init `untilEvent` nextStep
    where
    nextStep = do
        dt <- waitTimestep 0.033  -- XXX hardcoded
        v <- sample sig
        let !val = init ^+^ dt *^ v
        integral val sig

when :: Signal Bool -> Event ()
when cond = unsafeEventIO $ atomically $ do
    v <- readSignal cond
    if v then return () else retry

delay :: Double -> Event ()
delay t = waitTimestep t >> return ()

time :: Event (Signal Double)
time = time' 0
    where
    -- XXX another hardcoded
    time' (!t) = pure t `untilEvent` (waitTimestep 0.033 >>= time' . (+t))

loadImage :: FilePath -> Event Draw.Sprite
loadImage = unsafeEventIO . Draw.imageToSprite
