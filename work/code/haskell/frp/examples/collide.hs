{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl
import Control.Monad
import Data.Maybe

type Vec = (Double,Double)
data PhysIn =
    PhysIn { force   :: Vec
           , impulse :: Maybe Vec
           }
data PhysOut =
    PhysOut { position :: Vec
            , momentum :: Vec
            }

type Ball = PhysIn :=> PhysOut

newBall :: Vec -> Vec -> Double -> Ball
newBall ipos ivel mass = proc inp -> do
    avel <- (^+^ ivel) ^<< integral -< force inp ^/ mass
    imvel <- foldPulse (^+^) zero -< fmap (^/ mass) $ impulse inp
    let vel = avel ^+^ imvel
    pos  <- (^+^ ipos) ^<< integral -< vel
    returnA -< PhysOut { position = pos, momentum = mass *^ vel }

collide :: (PhysOut,PhysOut) :=> Maybe (PhysIn,PhysIn)
collide = proc ~(a,b) -> do
    let pdiff = position b ^-^ position a
    let vdiff = momentum b ^-^ momentum a
    lastvdiff <- delayStep zero -< vdiff

    let collision = guard $ norm pdiff < 2
                         && fst pdiff * fst lastvdiff + snd pdiff * snd lastvdiff < 0
    collisionSpark <- edgeToPulse -< collision

    -- if the spark happened, we compute these
    let impulse = projectTo pdiff vdiff
    returnA -< fmap (const $ (PhysIn zero (Just $ impulse)
                             ,PhysIn zero (Just $ (-1) *^ impulse))) 
                    collisionSpark

main = runGame defaultInit game

game = proc () -> do
    rec balla <- newBall (-5,0) (5,0) 1 -< fst collision'
        ballb <- newBall (5,1) (-1,0) 1 -< snd collision'
        collision <- collide -< (balla,ballb)
        let collision' = fromMaybe (dup $ PhysIn zero Nothing) collision
    returnA -< translate (position balla) unitCircle
            >> translate (position ballb) unitCircle

dup x = (x,x)
