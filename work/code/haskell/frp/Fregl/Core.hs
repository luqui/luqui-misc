{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Core 
    ( MouseButton(..)
    , MouseState(..)
    , EventVal(..)
    , integral
    , module Graphics.UI.SDL.Keysym
    )
where

import Fregl.Signal
import Fregl.Event
import Fregl.Vector
import qualified Fregl.Drawing as Draw
import Control.Applicative
import Debug.Trace
import Graphics.UI.SDL.Keysym

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
    waitKeyDown     :: Event e Keysym
    waitKeyUp       :: Event e Keysym



-- standard combinators

integral :: (EventVal e, Vector v, Field v ~ Double) 
         => v -> Signal v -> Event e (Signal v)
integral init sig = pure init `untilEvent` nextStep
    where
    nextStep = do
        dt <- waitTimestep
        v <- readSig sig
        integral (init ^+^ dt *^ v) sig
