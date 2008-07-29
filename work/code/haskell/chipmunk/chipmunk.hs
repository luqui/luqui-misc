import qualified Graphics.UI.SDL as SDL
import Graphics.Rendering.OpenGL.GL as GL
import Graphics.Rendering.OpenGL.GLU as GLU
import qualified Physics.Hipmunk as CP
import System.Random
import Control.Monad
import Debug.Trace
import Control.Applicative

bounds = ((-16.0,-12.0),(16.0,12.0))

initGfx = do
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    GL.matrixMode $= GL.Projection
    GL.loadIdentity
    GLU.ortho2D (-16) 16 (-12) 12
    GL.matrixMode $= GL.Modelview 0
    GL.loadIdentity

    CP.initChipmunk


main = do
    initGfx

    space <- CP.newSpace
    CP.setIterations space 2
    CP.setElasticIterations space 2
    CP.resizeActiveHash space 1 500

    addWall space (-16,-12) ( 16,-12)
    addWall space ( 16,-12) ( 16, 12)
    addWall space ( 16, 12) (-16, 12)
    addWall space (-16, 12) (-16,-12)

    balls <- forM [1..2000] $ \_ -> do
        body <- CP.newBody 1 1 -- mass, inertia
        (x,y) <- rand ((-4,0),(4,12))
        CP.setPosition body (CP.Vector x y)
        shape <- CP.newShape body (CP.Circle { CP.radius = 0.1 }) (CP.Vector 0 0)
        CP.setElasticity shape 0.99
        CP.applyForce body (CP.Vector 0 (-1)) (CP.Vector 0 0)
        CP.spaceAdd space body
        CP.spaceAdd space shape
        return body

    forever $ do
        GL.clear [GL.ColorBuffer]
        GL.pointSize $= 2
        GL.renderPrimitive GL.Points $ do
            forM balls $ \ball -> do
                CP.Vector x y <- CP.getPosition ball
                GL.vertex (GL.Vertex2 x y)
        SDL.glSwapBuffers
        CP.step space (1/30)


staticShape typ origin = do
    dummy <- CP.newBody CP.infinity CP.infinity
    CP.setPosition dummy (CP.Vector 0 0)
    CP.newShape dummy typ origin


addWall space (x1,y1) (x2,y2) = do
    shape <- staticShape (CP.LineSegment {
                   CP.start = CP.Vector x1 y1,
                   CP.end   = CP.Vector x2 y2,
                   CP.thickness = 0.1
                }) (CP.Vector 0 0)
    CP.setElasticity shape 0.99
    CP.spaceAdd space (CP.Static shape)


drawCircle (x,y) = GL.preservingMatrix $ do
    GL.translate (GL.Vector3 x y 0)
    GL.renderPrimitive GL.TriangleFan $ do
        GL.vertex (GL.Vertex2 0 0 :: GL.Vertex2 Double)
        forM_ [0..12::Double] $ \i -> do
            let theta = 2 * pi * i / 12
            GL.vertex (GL.Vertex2 (0.1 * cos theta) (0.1 * sin theta))


rand ((lx,ly),(hx,hy)) = do
    x <- randomRIO (lx,hx) 
    y <- randomRIO (ly,hy)
    return (x,y)
