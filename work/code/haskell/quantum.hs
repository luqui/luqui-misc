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

-- run these like: execQuantum detangle ()

detangle :: Quantum () ()
detangle = proc () -> do
    x <- makeStates -< ()
    qIO print -< x

detangle2 :: Quantum () ()
detangle2 = proc () -> do
    x <- makeStates -< ()
    qIO print -< x^2

perlExample :: Quantum () ()
perlExample = proc () -> do
    c <- entangle -< [(0, 1 :+ 0), (1, 0 :+ 1)] -- c = |0> + i|1>
    d <- entangle -< [(0, 1 :+ 0), (1, 1 :+ 0)] -- d = |0> + |1>
    let e = c * d  -- e = |0*0> + i|0*1> + |1*0> + i|1*1>
    if e == 1
        then qIO_ (putStrLn "e = 1") -< ()
        else qIO_ (putStrLn "e = 0") -< ()
    qIO putStrLn -< "(c,d) = " ++ show (c,d)
    
nonCollapsingConditional :: Quantum () ()
nonCollapsingConditional = proc () -> do
    x <- entangle -< [(1, 1 :+ 0), (2, (-1) :+ 0), (3, 0 :+ 1)]
    let y = if x == 2 then 1 else x
    qIO print -< y
