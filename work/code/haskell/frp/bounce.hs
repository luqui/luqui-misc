{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl
import Control.Arrow
import Control.Monad

bounce :: (Double,Double)   -- bounds
       -> Double            -- radius
       -> (Double,Double)   -- position, velocity
       :> Maybe Double      -- impulses
bounce (minBound,maxBound) radius = proc (pos,vel) -> do
    cleft'  <- edgeToPulse -< guard $ pos - radius < minBound
    cright' <- edgeToPulse -< guard $ pos + radius > maxBound
    let impulseLeft = fmap (const (2*abs vel)) cleft'
    let impulseRight = fmap (const (-2*abs vel)) cright'
    returnA -< impulseLeft `mplus` impulseRight
    

ball :: () :> Draw ()
ball = proc () -> do 
    rec y <- integralD -< y'
        let y' = gravity + impulsey + 11
        gravity <- integralD -< (-9.8)
        impulsey <- foldPulse (+) 0 <<< bounce (-12,12) 1 -< (y,y')
        x <- integralD -< x'
        let x' = impulsex + 9
        impulsex <- foldPulse (+) 0 <<< bounce (-16,16) 1 -< (x,x')
    returnA -< translate (x,y) unitCircle

main = runGame ball
