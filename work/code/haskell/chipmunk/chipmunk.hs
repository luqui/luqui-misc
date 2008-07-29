import qualified Graphics.UI.SDL as SDL
import Graphics.Rendering.OpenGL.GL as GL
import Graphics.Rendering.OpenGL.GLU as GLU
import qualified Physics.Hipmunk as CM
import System.Random
import Control.Monad
import Debug.Trace

bounds = ((-16.0,-12.0),(16.0,12.0))

initGfx = do
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    GL.matrixMode $= GL.Projection
    GL.loadIdentity
    GLU.ortho2D (-16) 16 (-12) 12
    GL.matrixMode $= GL.Modelview 0
    GL.loadIdentity

    CM.initChipmunk

rand ((lx,ly),(hx,hy)) = do
    x <- randomRIO (lx,hx) 
    y <- randomRIO (ly,hy)
    return (x,y)

main = do
    initGfx

    space <- CM.newSpace
    CM.setIterations space 4
    CM.setElasticIterations space 4
    CM.resizeActiveHash space 1 500

    addWall space (-16,-12) ( 16,-12)
    addWall space ( 16,-12) ( 16, 12)
    addWall space ( 16, 12) (-16, 12)
    addWall space (-16, 12) (-16,-12)

    balls <- forM [1..3000] $ \_ -> do
        body <- CM.newBody 1 1 -- mass, inertia
        (x,y) <- rand ((-4,0),(4,12))
        CM.setPosition body (CM.Vector x y)
        shape <- CM.newShape body (CM.Circle { CM.radius = 0.1 }) (CM.Vector 0 0)
        CM.setElasticity shape 0.99
        CM.applyForce body (CM.Vector 0 (-1)) (CM.Vector 0 0)
        CM.spaceAdd space body
        CM.spaceAdd space shape
        return body

    forever $ do
        GL.clear [GL.ColorBuffer]
        GL.renderPrimitive GL.Points $ do
            forM balls $ \ball -> do
                CM.Vector x y <- CM.getPosition ball
                GL.vertex (GL.Vertex2 x y)
        SDL.glSwapBuffers
        CM.step space (1/30)



addWall space (x1,y1) (x2,y2) = do
    dummy <- CM.newBody CM.infinity CM.infinity
    let pos = CM.Vector ((x1+x2)/2) ((y1+y2)/2)
    CM.setPosition dummy $ CM.Vector 0 0
    shape <- CM.newShape dummy (CM.LineSegment { 
                                 CM.start = CM.Vector x1 y1,
                                 CM.end   = CM.Vector x2 y2,
                                 CM.thickness = 0.1
                               }) (CM.Vector 0 0)
    CM.setElasticity shape 0.99
    CM.spaceAdd space dummy
    CM.spaceAdd space (CM.Static shape)


drawCircle (x,y) = GL.preservingMatrix $ do
    GL.translate (GL.Vector3 x y 0)
    GL.renderPrimitive GL.TriangleFan $ do
        GL.vertex (GL.Vertex2 0 0 :: GL.Vertex2 Double)
        forM_ [0..12::Double] $ \i -> do
            let theta = 2 * pi * i / 12
            GL.vertex (GL.Vertex2 (0.1 * cos theta) (0.1 * sin theta))
