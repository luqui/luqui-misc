{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Draw
    ( Drawing, runDrawing
    , Color
    , regularUnitNGon, unitCircle
    , rectangle
    , translate, scale, rotate
    , color
    )
where

import qualified Graphics.Rendering.OpenGL as GL
import qualified Control.Monad.Reader as Reader
import Data.Monoid

type Color = (Double,Double,Double)

newtype Drawing = Drawing { runDrawing :: IO () }

instance Monoid Drawing where
    mempty = Drawing $ return ()
    mappend = over

over :: Drawing -> Drawing -> Drawing
over (Drawing a) (Drawing b) = Drawing (b >> a)

under :: Drawing -> Drawing -> Drawing
under = flip over

regularUnitNGon :: Int -> Drawing
regularUnitNGon sides = Drawing $
    GL.renderPrimitive GL.TriangleFan $ do
        vertex2d 0 0
        mapM_ (\theta -> vertex2d (cos theta) (sin theta))
              $ map ((2*pi/fromIntegral sides)*) [0..fromIntegral sides]

unitCircle :: Drawing
unitCircle = regularUnitNGon 24

rectangle :: (Double,Double) -> Drawing
rectangle (w,h) = Drawing $ do
    let w' = 0.5*w
        h' = 0.5*h
    GL.renderPrimitive GL.Quads $ do
        vertex2d (-w') (-h')
        vertex2d ( w') (-h')
        vertex2d ( w') ( h')
        vertex2d (-w') ( h')

color :: Color -> Drawing -> Drawing
color c@(r,g,b) subdraw = Drawing $ do
    cur <- GL.get GL.currentColor
    GL.color (GL.Color3 r g b)
    result <- runDrawing subdraw
    GL.color cur
    return result

translate :: (Double,Double) -> Drawing -> Drawing
translate (x,y) d = Drawing $ GL.preservingMatrix $ do
    GL.translate (GL.Vector3 x y 0)
    runDrawing d

scale :: Double -> Double -> Drawing -> Drawing
scale x y d = Drawing $ GL.preservingMatrix $ do
    GL.scale x y 1
    runDrawing d

-- RADIANS, stupid opengl
rotate :: Double -> Drawing -> Drawing
rotate theta d = Drawing $ GL.preservingMatrix $ do
    GL.rotate (theta*180/pi) (GL.Vector3 0 0 1)
    runDrawing d


vertex2d :: Double -> Double -> IO ()
vertex2d x y = GL.vertex (GL.Vertex2 x y)
