{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

import Control.Arrow
import FRP
import Debug.Trace

main = runFRP whee

whee :: () :> Draw ()
whee = proc () -> do
    mousepos <- mousePos -< ()
    rec let x' = fst mousepos - x
        let y' = snd mousepos - y
        x  <- integral 0 -< x'
        y  <- integral 0 -< y'
    returnA -< translate (x,y) $ unitCircle
