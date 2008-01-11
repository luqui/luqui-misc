module Fregl.Core 
    ( MouseButton(..)
    , MouseState(..)
    , EventVal(..)
    , integral
    )
where

import Fregl.Signal
import Fregl.Event
import qualified Fregl.Drawing as Draw
import Control.Applicative

-- interface for Fregl cores

data MouseButton
    = ButtonLeft
    | ButtonRight
    deriving Eq

data MouseState
    = MouseUp
    | MouseDown
    deriving Eq

class EventVal e where
    wait            :: Event e ()
    waitTimestep    :: Event e Double
    waitMouseMotion :: Event e (Double,Double)
    waitClickPos    :: MouseButton -> MouseState -> Event e (Double,Double)
    waitClickName   :: MouseButton -> MouseState -> Draw.Name -> Event e (Double,Double)



-- standard combinators

integral :: (EventVal e) => Double -> Signal Double -> Event e (Signal Double)
integral init sig = pure init `untilEvent` nextStep
    where
    nextStep = do
        dt <- waitTimestep
        v <- readSig sig
        integral (init + dt * v) sig
