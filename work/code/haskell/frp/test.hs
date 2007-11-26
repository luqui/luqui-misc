{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

import Control.Arrow
import FRP
import Debug.Trace

main = runFRP whee

whee :: () :> Draw ()
whee = proc () -> do
    (mousex,mousey) <- mousePos -< ()
    rec let x' = mousex - x
        let y' = mousey - y
        x  <- integral 0 -< x'
        y  <- integral 0 -< y'
    returnA -< translate (x,y) $ unitCircle
