{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Draw
    ( Draw, runDraw
    , regularUnitNGon, unitCircle
    , translate, scale, rotate
    )
where

import qualified Graphics.Rendering.OpenGL as GL

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
