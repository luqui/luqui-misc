{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Drawing 
    ( Drawing, runDrawing
    , point, line, regularPoly, circle
    , translate, rotate, scale
    , Name, name, getName, makeName
    , Color, color, colorFunc
    )
where

import Fregl.Splittable
import Fregl.LinearSplit
import Fregl.Vector
import Data.Monoid
import Control.Monad
import Control.Monad.Reader
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

type Color = Vec4

newtype Drawing = Drawing { unDrawing :: ReaderT DrawCxt IO () }

runDrawing :: Drawing -> IO ()
runDrawing d = runReaderT (unDrawing d) initDrawCxt

data DrawCxt 
    = DrawCxt { colorTrans :: Color -> Color }

initDrawCxt = DrawCxt { colorTrans = id }

instance Monoid Drawing where
    mempty = Drawing $ return ()
    mappend (Drawing a) (Drawing b) = Drawing $ a >> b

newtype Name = Name { getName :: LinearSplit GL.Name }
                deriving Splittable

makeName :: IO Name
makeName = fmap Name $ newLinearSplit $ map GL.Name [0..]

name :: Name -> Drawing -> Drawing
name (Name n) d = Drawing $ do
    n' <- lift $ readLinearSplit n
    r <- ask
    lift $ GL.withName n' $ runReaderT (unDrawing d) r

point :: Vec2 -> Drawing
point (ax,ay) = Drawing $ lift $
    GL.renderPrimitive GL.Points $
        GL.vertex $ GL.Vertex2 ax ay

line :: Vec2 -> Vec2 -> Drawing
line (ax,ay) (bx,by) = Drawing $ lift $ 
    GL.renderPrimitive GL.Lines $ do
        GL.vertex $ GL.Vertex2 ax ay
        GL.vertex $ GL.Vertex2 bx by

regularPoly :: Int -> Drawing
regularPoly n = Drawing $ lift $ do
    let scaler :: Double = 2 * pi / fromIntegral n
    GL.renderPrimitive GL.TriangleFan $ do
        GL.vertex $ (GL.Vertex2 0 0 :: GL.Vertex2 Double)
        forM_ [0..n] $ \s -> do
            let theta = scaler * fromIntegral s
            GL.vertex $ GL.Vertex2 (cos theta) (sin theta)

circle :: Drawing
circle = regularPoly 24

translate :: Vec2 -> Drawing -> Drawing
translate (byx,byy) d = Drawing $ do
    r <- ask
    lift $ GL.preservingMatrix $ do
        GL.translate (GL.Vector3 byx byy 0)
        runReaderT (unDrawing d) r

rotate :: Double -> Drawing -> Drawing
rotate rad d = Drawing $ do
    r <- ask
    lift $ GL.preservingMatrix $ do
        GL.rotate (180 * rad / pi) (GL.Vector3 0 0 1)
        runReaderT (unDrawing d) r

scale :: Double -> Double -> Drawing -> Drawing
scale x y d = Drawing $ do
    r <- ask
    lift $ GL.preservingMatrix $ do
        GL.scale x y 1
        runReaderT (unDrawing d) r

colorFunc :: (Color -> Color) -> Drawing -> Drawing
colorFunc cf d = Drawing $ do
    r <- ask
    let cf' = colorTrans r . cf
    let oldcolor = colorTrans r (1,1,1,1)
    let newcolor = colorTrans r $ cf (1,1,1,1)
    local (const (r { colorTrans = cf' })) $ do
        setColor newcolor
        unDrawing d
    setColor oldcolor
    where
    setColor (r,g,b,a) = lift $ GL.color $ GL.Color4 r g b a

color :: Color -> Drawing -> Drawing
color c = colorFunc (const c)
