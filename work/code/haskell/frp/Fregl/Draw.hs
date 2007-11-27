{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Draw
    ( Draw, runDraw
    , Color
    , regularUnitNGon, unitCircle
    , rectangle
    , translate, scale, rotate
    , color
    )
where

import qualified Graphics.Rendering.OpenGL as GL
import qualified Control.Monad.Reader as Reader

type Color = (Double,Double,Double)

newtype Draw a = Draw { runDraw :: IO a }
    deriving (Functor, Monad)

regularUnitNGon :: Int -> Draw ()
regularUnitNGon sides = Draw $
    GL.renderPrimitive GL.TriangleFan $ do
        vertex2d 0 0
        mapM_ (\theta -> vertex2d (cos theta) (sin theta))
              $ map ((2*pi/fromIntegral sides)*) [0..fromIntegral sides]

unitCircle :: Draw ()
unitCircle = regularUnitNGon 24

rectangle :: (Double,Double) -> Draw ()
rectangle (w,h) = Draw $ do
    let w' = 0.5*w
        h' = 0.5*h
    GL.renderPrimitive GL.Quads $ do
        vertex2d (-w') (-h')
        vertex2d ( w') (-h')
        vertex2d ( w') ( h')
        vertex2d (-w') ( h')

color :: Color -> Draw a -> Draw a
color c@(r,g,b) subdraw = Draw $ do
    cur <- GL.get GL.currentColor
    GL.color (GL.Color3 r g b)
    result <- runDraw subdraw
    GL.color cur
    return result

translate :: (Double,Double) -> Draw a -> Draw a
translate (x,y) d = Draw $ GL.preservingMatrix $ do
    GL.translate (GL.Vector3 x y 0)
    runDraw d

scale :: Double -> Double -> Draw a -> Draw a
scale x y d = Draw $ GL.preservingMatrix $ do
    GL.scale x y 1
    runDraw d

-- RADIANS, stupid opengl
rotate :: Double -> Draw a -> Draw a
rotate theta d = Draw $ GL.preservingMatrix $ do
    GL.rotate (theta*180/pi) (GL.Vector3 0 0 1)
    runDraw d


vertex2d :: Double -> Double -> IO ()
vertex2d x y = GL.vertex (GL.Vertex2 x y)
