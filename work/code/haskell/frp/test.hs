{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

import Control.Arrow
import FRP
import Debug.Trace

main = runFRP whee

whee :: () :> Draw ()
whee = proc () -> do
    x <- pure cos <<< time -< ()
    y <- pure sin <<< time -< ()
    returnA -< translate (x,y) $ unitCircle
