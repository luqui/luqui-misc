{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Quantum
import Control.Arrow
import Data.Complex

makeStates :: Quantum () Int
makeStates = proc () -> 
    entangle -< [( 4,   1  :+ 0)
                ,(-4, (-1) :+ 0)
                ,( 3,   0  :+ 1)
                ]

detangle :: Quantum () ()
detangle = proc () -> do
    x <- makeStates -< ()
    qPutStr -< show x ++ "\n"

detangle2 :: Quantum () ()
detangle2 = proc () -> do
    x <- makeStates -< ()
    qPutStr -< show (x^2) ++ "\n"

dett :: Quantum () () -> IO ()
dett ar = do
    runQuantum ar ()
    return ()
