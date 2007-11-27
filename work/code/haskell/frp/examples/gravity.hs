{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl
import qualified Graphics.UI.SDL as SDL
import Data.List (foldl')
import Debug.Trace
import Control.Monad

type Vec = Vec2 Double

main = runGame defaultInit
          $ balls
        >>> arr (map (\p -> translate p unitCircle))
        >>> arr (foldr (>>) (return ()))

balls :: () :=> [Vec]
balls = mouseButtonDown SDL.ButtonLeft
        >>> edgeToPulse
        >>> arr (fmap ball)
        >>> joinSF

ball :: Vec -> [Vec] :=> Vec
ball initpos = proc ballpos -> do
    rec pos <- (^+^ initpos) ^<< integral -< vel
        vel <- returnA -< impulse ^+^ velBound 50 velFromAccel
        velFromAccel <- integral -< accel
        
        let accel = 10 *^ (foldl' (^+^) zero $ map (forceFrom pos) ballpos)
        impulse <- foldPulse (^+^) zero <<< bounce -< (pos,vel)
    returnA -< pos

    where
    forceFrom self pos = 
        if self == pos 
           then zero
           else unitize (pos ^-^ self) ^* (1 / norm2 (pos ^-^ self))

velBound :: Double -> Vec -> Vec
velBound max v = 
    if norm v > max
       then max *^ unitize v
       else v

bounce1d :: (Double,Double) -> Double -> (Double,Double) :=> Maybe Double
bounce1d (minBound, maxBound) radius = proc (pos,vel) -> do
    leftHit  <- edgeToPulse -< guard (pos - radius < minBound)
    rightHit <- edgeToPulse -< guard (pos + radius > maxBound)
    let leftBounce  = fmap (const (2*abs vel))  leftHit
    let rightBounce = fmap (const (-2*abs vel)) rightHit
    returnA -< leftBounce `mplus` rightBounce

bounce :: (Vec,Vec) :=> Maybe Vec
bounce = proc (~(posx,posy),~(velx,vely)) -> do
    xb <- bounce1d (-16,16) 1 -< (posx,velx)
    yb <- bounce1d (-12,12) 1 -< (posy,vely)
    returnA -< case (xb,yb) of
                    (Nothing,Nothing) -> Nothing
                    (Just x,Nothing)  -> Just (x,0)
                    (Nothing,Just y)  -> Just (0,y)
                    (Just x, Just y)  -> Just (x,y)
