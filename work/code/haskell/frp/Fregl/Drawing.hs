module Fregl.Drawing where

import Fregl.Vector
import Data.Monoid
import Control.Monad
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

newtype Drawing = Drawing { runDrawing :: IO () }

instance Monoid Drawing where
    mempty = Drawing $ return ()
    mappend (Drawing a) (Drawing b) = Drawing $ a >> b

point :: Vec2 -> Drawing
point (ax,ay) = Drawing $
    GL.renderPrimitive GL.Points $
        GL.vertex $ GL.Vertex2 ax ay

line :: Vec2 -> Vec2 -> Drawing
line (ax,ay) (bx,by) = Drawing $ do
    GL.renderPrimitive GL.Lines $ do
        GL.vertex $ GL.Vertex2 ax ay
        GL.vertex $ GL.Vertex2 bx by

regularPoly :: Int -> Drawing
regularPoly n = Drawing $ do
    let scale = 2 * pi / fromIntegral n
    GL.renderPrimitive GL.TriangleFan $ do
        GL.vertex $ (GL.Vertex2 0 0 :: GL.Vertex2 Double)
        forM_ [0..n] $ \s -> do
            let theta :: Double = scale * fromIntegral s
            GL.vertex $ GL.Vertex2 (cos theta) (sin theta)

circle :: Drawing
circle = regularPoly 24
