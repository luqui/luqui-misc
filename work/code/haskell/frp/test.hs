{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

import Control.Arrow
import FRP
import Debug.Trace
import qualified Graphics.UI.SDL as SDL

main = runFRP circlePlacer


circlePlacer :: () :> Draw ()
circlePlacer = 
    mouseButtonDown SDL.ButtonLeft >>> edgeToPulse >>> arr (fmap newCircle) >>> joinSF >>^ sequence_

newCircle :: (Double, Double) -> () :> Draw ()
newCircle init = proc () -> do
    mouse <- mousePos -< ()
    rec let u' = mouse ^-^ u
        u  <- (^+^ init) ^<< integral -< u'

    big <- keyDown SDL.SDLK_SPACE -< ()
    let scaler = if isJust big then scale 2 2 else id
    returnA -< translate u $ scaler $ unitCircle

