{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl
import Control.Monad
import Data.Maybe
import Data.List

type Vec = (Double,Double)
data PhysIn =
    PhysIn { force   :: Vec
           , impulse :: Maybe Vec
           }
data PhysOut =
    PhysOut { position :: Vec
            , momentum :: Vec
            }

addIn :: PhysIn -> PhysIn -> PhysIn
addIn (PhysIn f i) (PhysIn f' i') = PhysIn (f ^+^ f') (addImpulse i i')
    where
    addImpulse Nothing  Nothing   = Nothing
    addImpulse (Just i) Nothing   = Just i
    addImpulse Nothing  (Just i') = Just i'
    addImpulse (Just i) (Just i') = Just (i ^+^ i')

type Ball = PhysIn :=> PhysOut

newBall :: Vec -> Vec -> Double -> Ball
newBall ipos ivel mass = proc inp -> do
    avel <- (^+^ ivel) ^<< integral zero -< force inp ^/ mass
    imvel <- foldPulse (^+^) zero -< fmap (^/ mass) $ impulse inp
    let vel = avel ^+^ imvel
    pos  <- (^+^ ipos) ^<< integral zero -< vel
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

mapA :: (a :=> b) -> [a] :=> [b]
mapA f = proc inp -> do
    case inp of
         []     -> returnA -< []
         (x:xs) -> do
            x'  <- f      -< x
            xs' <- mapA f -< xs
            returnA -< (x':xs')

insertBall :: PhysIn :=> PhysOut -> [PhysIn] :=> [PhysOut] -> [PhysIn] :=> [PhysOut]
insertBall b bs = proc ~(inp:inps) -> do
    rec bout  <- b  -< foldl' addIn inp $ map fst collides'
        bouts <- bs -< zipWith addIn inps $ map snd collides'
        collides <- mapA collide -< map ((,) bout) bouts
        let collides' = map (fromMaybe (dup $ PhysIn zero Nothing)) collides
    returnA -< (bout:bouts)


newBalls :: [PhysIn :=> PhysOut] -> [PhysIn] :=> [PhysOut]
newBalls = foldr insertBall (constSF [])

game = proc () -> do
    bs <- newBalls [ newBall (-5,0) (5,0) 1
                   , newBall (5,1) (-1,0) 1
                   , newBall (0,5) (0.5,-2.6) 1] -< [noIn,noIn,noIn]
    let positions = map position bs
    returnA -< foldl' (>>) (return ()) 
                      (map (\p -> translate p unitCircle) positions)
    where
    noIn = PhysIn zero Nothing

dup x = (x,x)
