{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

import Control.Arrow
import Fregl
import Debug.Trace
import qualified Graphics.UI.SDL as SDL

main = runGame circlePlacer


circlePlacer :: () :> Draw ()
circlePlacer = 
    mouseButtonDown SDL.ButtonLeft     -- the state of the left mouse button
           >>> edgeToPulse             -- convert to clicks
           >>> pure (fmap newCircle)   -- make a new circle at the clicked position
           >>> joinSF                  -- make a list of all created circles
           >>> pure sequence_          -- combine them into one drawing

newCircle :: (Double, Double) -> a :> Draw ()
newCircle init = proc _ -> do
    mouse <- mousePos -< ()
    rec let u' = mouse ^-^ u
        u  <- (^+^ init) ^<< integral -< u'

    big <- keyDown SDL.SDLK_SPACE -< ()
    let scaler = if isJust big then scale 2 2 else id
    returnA -< color (1,0,0) $ translate u $ scaler $ unitCircle

