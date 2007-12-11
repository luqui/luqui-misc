{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Physics
    ( BodyID
    , World
    , emptyWorld
    , trajectory
    , newBody, deleteBody
    , bodyPosition, bodyVelocity
    , bodyAngle, bodyAngVel
    , bodyMass, bodyMoment
    , force, forceAt
    , impulse, impulseAt
    , torque, torqueImpulse
    )
where

import Fregl.Vector
import Fregl.Differentiable
import qualified Data.Map as Map

data BodyState
    = BodyState { bPosition :: Vec2 Double
                , bVelocity :: Vec2 Double
                , bRotation :: Double
                , bAngVel   :: Double
                }

data DBody
    = DBody { dbPosition :: Vec2 Double
            , dbVelocity :: Vec2 Double
            , dbLImpulse :: Vec2 Double
            , dbRotation :: Double
            , dbAngVel   :: Double
            , dbAImpulse :: Double
            }


instance Vector DBody where
    type Field DBody = Double
    zero = DBody zero zero zero 0 0 0
    DBody p v li r a ai ^+^ DBody p' v' li' r' a' ai'
        = DBody (p ^+^ p') (v ^+^ v') (li ^+^ li')
                (r + r')   (a + a')   (ai + ai')
    -- not sure whether x should scale impulses or not
    -- Probably ill-defined and need to rethink anyway
    x *^ DBody p v li r a ai
        = DBody (x *^ p) (x *^ v) (x *^ li)
                (x * r)  (x * a)  (x * ai)

data Body
    = Body { bState  :: BodyState
           , bMass   :: Double
           , bMoment :: Double
           }

instance Differentiable Body where
    type Diff Body = DBody
    integrate dt d b = b { bState = newState  (bState b) }
        where
        newState b = BodyState 
            { bPosition = dt *^ dbPosition d ^+^ bPosition b
            , bVelocity = dt *^ dbVelocity d ^+^ dbLImpulse d ^+^ bVelocity b
            , bRotation = dt *  dbRotation d  +  bRotation b
            , bAngVel   = dt *  dbAngVel d    +  dbAImpulse d  +  bAngVel b 
            }

    infsIntegrate d b = b { bState = newState (bState b) }
        where
        newState b = b
            { bVelocity = dbLImpulse d ^+^ bVelocity b
            , bAngVel   = dbAImpulse d  +  bAngVel b
            }


bTrajectory :: Body -> Diff Body
bTrajectory b = 
    DBody { dbPosition = bVelocity (bState b)
          , dbVelocity = zero
          , dbLImpulse = zero
          , dbRotation = bAngVel (bState b)
          , dbAngVel   = 0
          , dbAImpulse = 0
          }


newtype BodyID = BodyID Int
    deriving (Eq,Ord)

data World
    = World { wMap :: Map.Map BodyID Body
            , wFreeList :: [BodyID]
            }

data DWorld
    = DWorld { dwMap :: Map.Map BodyID (Diff Body) }

instance Differentiable World where
    type Diff World = DWorld
    integrate dt dw w =
        w { wMap = Map.differenceWith 
                    (\b d -> Just $ integrate dt d b) 
                    (wMap w) (dwMap dw) 
          }

emptyWorld = World { wMap = Map.empty
                   , wFreeList = map BodyID [0..]
                   }

trajectory :: World -> Diff World
trajectory w = 
    DWorld { dwMap = Map.map bTrajectory (wMap w) }

newBody :: Double -> Double            -- mass, moment
        -> Vec2 Double -> Vec2 Double  -- position, velocity
        -> Double -> Double            -- rotation, angular velocity
        -> World -> (BodyID,World)
newBody mass moment pos vel rot angvel world
    = (newId, newWorld)
    where
    newWorld = World { wMap = Map.insert newId newBody (wMap world)
                     , wFreeList = newList
                     }
    newId:newList = wFreeList world
    newBody = Body { bState = BodyState 
                        { bPosition = pos
                        , bVelocity = vel
                        , bRotation = rot
                        , bAngVel   = angvel
                        }
                   , bMass = mass
                   , bMoment = moment
                   }

deleteBody :: BodyID -> World -> World
deleteBody bid world =
    World { wMap      = Map.delete bid (wMap world)
          , wFreeList = (if deleted then (bid:) else id) (wFreeList world)
          }
    where
    -- got to make sure we actually deleted something
    -- otherwise we'll have a duplicate in the free list
    deleted = bid `Map.member` wMap world

stAccess :: (Body -> a) -> World -> BodyID -> a
stAccess f w b = f (wMap w Map.! b)

bodyPosition = stAccess (bPosition . bState)
bodyVelocity = stAccess (bVelocity . bState)
bodyAngle    = stAccess (bRotation . bState)
bodyAngVel   = stAccess (bAngVel   . bState)
bodyMass     = stAccess bMass
bodyMoment   = stAccess bMoment

bodyMod :: BodyID -> Diff Body -> Diff World
bodyMod b d = DWorld { dwMap = Map.singleton b d }

force :: World -> BodyID -> Vec2 Double -> Diff World
force w b f = bodyMod b $ 
    zero { dbVelocity = f ^/ bodyMass w b }

forceAt :: World -> BodyID -> Vec2 Double -> Vec2 Double -> Diff World
forceAt w b f p = bodyMod b $ 
    zero { dbVelocity = f ^/ bodyMass w b
         , dbAngVel   = (r `cross2d` f) ^/ bodyMoment w b
         }
    where
    r = p ^-^ bodyPosition w b

impulse :: World -> BodyID -> Vec2 Double -> Diff World
impulse w b i = bodyMod b $ 
    zero { dbLImpulse = i ^/ bodyMass w b }

impulseAt :: World -> BodyID -> Vec2 Double -> Vec2 Double -> Diff World
impulseAt w b i p = bodyMod b $ 
    zero { dbLImpulse = i ^/ bodyMass w b
         , dbAImpulse = (r `cross2d` i) ^/ bodyMoment w b
         }
    where
    r = p ^-^ bodyPosition w b

torque :: World -> BodyID -> Double -> Diff World
torque w b t = bodyMod b $ 
    zero { dbAngVel = t ^/ bodyMoment w b }

torqueImpulse :: World -> BodyID -> Double -> Diff World
torqueImpulse w b t = bodyMod b $ 
    zero { dbAImpulse = t ^/ bodyMoment w b }
