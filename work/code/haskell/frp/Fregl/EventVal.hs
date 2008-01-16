module Fregl.EventVal where

import qualified Graphics.Rendering.OpenGL.GL as GL
import Graphics.UI.SDL.Keysym
import Control.Concurrent.STM
import Fregl.WFQueue
import Fregl.Vector

data MouseButton
    = ButtonLeft
    | ButtonRight
    deriving Eq

data MouseState
    = MouseUp
    | MouseDown
    deriving Eq

data EventVal 
    = MouseEvent MouseEvent Vec2 [GL.Name]
    | KeyDownEvent Keysym
    | KeyUpEvent Keysym

data MouseEvent
    = MouseButton MouseButton MouseState
    | MouseMotion


newtype EventWait
    = EventWait { ewait :: TReader EventVal }

duplicate :: EventWait -> IO EventWait
duplicate (EventWait ew) = do
    atomically $ fmap EventWait $ dupWFReader ew
