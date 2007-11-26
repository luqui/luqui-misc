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
newCircle (initx,inity) = proc () -> do
    (mousex,mousey) <- mousePos -< ()
    rec let x' = mousex - x
        let y' = mousey - y
        x  <- integral initx -< x'
        y  <- integral inity -< y'

    big <- keyDown SDL.SDLK_SPACE -< ()
    let scaler = if isJust big then scale 2 2 else id
    returnA -< translate (x,y) $ scaler $ unitCircle

