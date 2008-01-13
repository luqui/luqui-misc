{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Drawing 
    ( Drawing, runDrawing
    , point, line, regularPoly, circle
    , translate, rotate, scale
    , Name, name, getName, makeName
    , Color, color, colorFunc
    , imageToSprite, sprite
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
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.UI.SDL.Image as Image
import System.Mem.Weak
import Data.IORef 
import System.IO.Unsafe

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

--

data Sprite = Sprite { spriteObject :: GL.TextureObject }

-- FUUUUUUUUUCKKK Why doesn't glGenTextures work!!??
-- Anyway here is me hacking around it...
textureHack :: IORef [GL.GLuint]
textureHack = unsafePerformIO $ newIORef [1..]

allocateTexture :: IO GL.TextureObject
allocateTexture = do
    {- -- This is how it *should* be done.  wtf is going on!?
    [obj] <- GL.genObjectNames 1
    good <- GL.isObjectName obj
    unless good $ fail "Failed to generate valid object wtf!"
    return obj
    -}
    b <- atomicModifyIORef textureHack (\(x:xs) -> (xs,x))
    return $ GL.TextureObject b

freeTexture :: GL.TextureObject -> IO ()
freeTexture (GL.TextureObject b) = do
    GL.deleteObjectNames [GL.TextureObject b]
    modifyIORef textureHack (b:)


surfaceToSprite :: SDL.Surface -> IO Sprite
surfaceToSprite surf = do
    unless (isPowerOf2 (SDL.surfaceGetWidth  surf) 
         && isPowerOf2 (SDL.surfaceGetHeight surf)) $ do
             fail "Image's area is not a power of two!"
    obj <- allocateTexture
    oldtex <- GL.get (GL.textureBinding GL.Texture2D)
    GL.textureBinding GL.Texture2D GL.$= Just obj
    pixels <- SDL.surfaceGetPixels surf
    bytesPerPixel <- SDL.pixelFormatGetBytesPerPixel (SDL.surfaceGetPixelFormat surf)
    let pixelFormat = case bytesPerPixel of
                        3 -> GL.RGB
                        4 -> GL.RGBA
    GL.textureFunction GL.$= GL.Modulate
    GL.textureFilter GL.Texture2D GL.$= ((GL.Linear', Nothing), GL.Linear')
    GL.textureWrapMode GL.Texture2D GL.S GL.$= (GL.Mirrored, GL.Repeat)
    GL.textureWrapMode GL.Texture2D GL.T GL.$= (GL.Mirrored, GL.Repeat)
    GL.texImage2D Nothing GL.NoProxy 0 (GL.RGBA')  -- ? proxy level internalformat
                  (GL.TextureSize2D 
                    (fromIntegral $ SDL.surfaceGetWidth surf)
                    (fromIntegral $ SDL.surfaceGetHeight surf))
                  0 -- border
                  (GL.PixelData pixelFormat GL.UnsignedByte pixels)
    GL.textureBinding GL.Texture2D GL.$= oldtex
    let sprite = Sprite obj
    addFinalizer sprite $ do
        freeTexture obj
    return sprite
    where
    isPowerOf2 x = x == (last $ takeWhile (<= x) $ iterate (*2) 1)

imageToSprite :: FilePath -> IO Sprite
imageToSprite path = Image.load path >>= surfaceToSprite

sprite :: Sprite -> Drawing
sprite spr = Drawing $ liftIO $ do
    oldtex <- GL.get (GL.textureBinding GL.Texture2D)
    GL.textureBinding GL.Texture2D GL.$= (Just $ spriteObject spr)
    GL.renderPrimitive GL.Quads $ do
        tex 0 0  >>  vertex (-0.5)   0.5
        tex 1 0  >>  vertex   0.5    0.5
        tex 1 1  >>  vertex   0.5  (-0.5)
        tex 0 1  >>  vertex (-0.5) (-0.5)
    GL.textureBinding GL.Texture2D GL.$= oldtex
    where
    tex x y = GL.texCoord (GL.TexCoord2 x (y :: Double))
    vertex x y = GL.vertex (GL.Vertex2 x (y :: Double))

