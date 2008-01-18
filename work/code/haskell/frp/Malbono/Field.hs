{-# OPTIONS_GHC -fglasgow-exts #-}

module Malbono.Field where

import qualified Fregl.Vector as V
import qualified Fregl.Drawing as Draw
import qualified Graphics.Rendering.OpenGL.GL as GL
import Data.Array.IArray
import Data.Array.ST
import Control.Monad.ST
import Control.Monad

data Field a 
    = Field { fieldLL     :: V.Vec2
            , fieldDX     :: Double
            , fieldDY     :: Double
            , fieldWidth  :: Int
            , fieldHeight :: Int
            , fieldValues :: Array (Int,Int) a
            }

newField :: (Int,Int) -> V.Vec2 -> V.Vec2 -> a -> Field a
newField (w,h) ll (w',h') a
    = Field { fieldLL = ll
            , fieldDX = w' / fromIntegral w
            , fieldDY = h' / fromIntegral h
            , fieldWidth = w
            , fieldHeight = h
            , fieldValues = accumArray const a ((0,0),(w-1,h-1)) []
            }

balanceField :: forall v. (V.Vector v, V.Field v ~ Double)
             => (V.Vec2 -> v -> v) -- view function
             -> Double             -- diffusion constant
             -> Field v
             -> Field v
balanceField view dt field = field { fieldValues = newA }
    where
    viewA :: Array (Int,Int) v
    viewA = array ((0,0), (width-1, height-1)) $ do
                i <- [0..width-1]
                j <- [0..height-1]
                let pos = fieldLL field V.^+^
                      (dx * fromIntegral i, dy * fromIntegral j)
                return ((i,j), view pos (vals ! (i,j)))

    newA :: Array (Int,Int) v
    newA = vals // do
                i <- [1..width-2]
                j <- [1..height-2]
                let out = 0.25 * (1-dt)
                    left  = viewA ! (i-1,j)
                    right = viewA ! (i+1,j)
                    up    = viewA ! (i,j+1)
                    down  = viewA ! (i,j-1)
                    here  = viewA ! (i,j)
                    new   = out V.*^ (left V.^+^ right V.^+^ up V.^+^ down) V.^+^ dt V.*^ here
                    diff  = new V.^-^ here
                return ((i,j), (vals ! (i,j)) V.^+^ diff)
    
    width = fieldWidth field
    height = fieldHeight field
    dx = fieldDX field
    dy = fieldDY field
    vals = fieldValues field

drawField :: (v -> Draw.Color) -> Field v -> Draw.Drawing
drawField colf field = Draw.unsafeDraw $ do
    GL.renderPrimitive GL.Quads $ do
        forM_ [0..fieldWidth field-2] $ \i ->
            forM_ [0..fieldHeight field-2] $ \j -> do
                drawVertex (i  ,j)
                drawVertex (i+1,j)
                drawVertex (i+1,j+1)
                drawVertex (i  ,j+1)
    where
    drawVertex (x,y) = do
        let (r,g,b,a) = colf (vals ! (x,y))
        GL.color (GL.Color4 r g b a)
        GL.vertex (GL.Vertex2 (x0+dx*fromIntegral x) (y0+dy*fromIntegral y))

    Field { fieldLL = (x0,y0)
          , fieldDX = dx
          , fieldDY = dy
          , fieldValues = vals
          } = field
