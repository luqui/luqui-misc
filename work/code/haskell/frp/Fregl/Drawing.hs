module Fregl.Drawing where

import Fregl.Vector
import Data.Monoid
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

newtype Drawing = Drawing { runDrawing :: IO () }

instance Monoid Drawing where
    mempty = Drawing $ return ()
    mappend (Drawing a) (Drawing b) = Drawing $ a >> b

drawLine :: Vec2 -> Vec2 -> Drawing
drawLine (ax,ay) (bx,by) = Drawing $ do
    GL.renderPrimitive GL.Lines $ do
        GL.vertex $ GL.Vertex2 ax ay
        GL.vertex $ GL.Vertex2 bx by
