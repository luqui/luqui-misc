{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Quantum
import Control.Arrow
import Data.Complex

detangle :: Quantum (String,String) ()
detangle = proc (x,y) -> do
    qCheatInspect -< (x,y)
    qPutStr -< show (x,y) ++ "\n"
    qCheatInspect -< (x,y)
    qPutStr -< x ++ "\n"
    qCheatInspect -< (x,y)
    qPutStr -< y ++ "\n"

dett :: IO ()
dett = do
    runQuantum detangle 
        [(("hello","world"), 1 :+ 0), 
         (("hello","dumbass"), 1 :+ 0), 
         (("goodbye","cruel world"), 1 :+ 0)]
    return ()
