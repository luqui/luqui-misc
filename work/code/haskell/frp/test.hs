{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

import FRP
import Debug.Trace

main :: IO ()
main = runFRP $ fmap (\x' -> translate (x',0) unitCircle) xpos
    where
    xpos = integral 0 (fmap (trace "waah" . (+1)) xpos)
