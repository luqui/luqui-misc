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
            , velocity :: Vec
            }

type Ball = PhysIn :=> PhysOut

newBall :: Vec -> Vec -> Ball
newBall ipos ivel = proc inp -> do
    avel <- (^+^ ivel) ^<< integral -< force inp
    imvel <- foldPulse (^+^) zero -< impulse inp
    let vel = avel ^+^ imvel
    pos  <- (^+^ ipos) ^<< integral -< vel
    returnA -< PhysOut { position = pos, velocity = vel }

collide :: (PhysOut,PhysOut) :=> Maybe (PhysIn,PhysIn)
collide = proc ~(a,b) -> do
    let pamb = position b ^-^ position a
    lastvd <- delayStep zero -< velocity b ^-^ velocity a
    let collision = guard $ norm (position a ^-^ position b) < 2
                         && fst pamb * fst lastvd + snd pamb * snd lastvd < 0
    collision' <- edgeToPulse -< collision
    let cnorm = unitize (position b ^-^ position a)
    let imp = ((velocity b ^-^ velocity a) ^*^ cnorm) *^ cnorm
    returnA -< fmap (const $ (PhysIn zero (Just $ imp)
                             ,PhysIn zero (Just $ (-1) *^ imp))) collision'

main = runGame defaultInit game

game = proc () -> do
    rec balla <- newBall (-5,0) (5,0) -< fst collision'
        ballb <- newBall (5,1) (-1,0) -< snd collision'
        collision <- collide -< (balla,ballb)
        let collision' = fromMaybe (dup $ PhysIn zero Nothing) collision
    returnA -< translate (position balla) unitCircle
            >> translate (position ballb) unitCircle

dup x = (x,x)
