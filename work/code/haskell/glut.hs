import Graphics.UI.GLUT
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU
import Data.IORef

initScreen :: IO ()
initScreen = do
    GL.matrixMode $= GL.Projection
    GLU.ortho2D (-8) 8 (-6) 6
    GL.matrixMode $= GL.Modelview 0

-- wtf, why such the pain
glVertex2f :: GLfloat -> GLfloat -> IO ()
glVertex2f x y = GL.vertex (GL.Vertex2 x y)

glColor3f :: GLfloat -> GLfloat -> GLfloat -> IO ()
glColor3f r g b = GL.color (GL.Color3 r g b)

draw :: GLfloat -> IO ()
draw rot = do
    glColor3f 1 1 1
    GL.rotate rot (GL.Vector3 0 0 1)
    GL.renderPrimitive GL.Triangles $ do
        glVertex2f (-4) (-4)
        glVertex2f 4    (-4)
        glVertex2f 0    4

redraw :: Window -> IORef GLfloat -> IO ()
redraw win rot = do
    GL.loadIdentity
    GL.clear [GL.ColorBuffer]
    rotation <- readIORef rot
    draw rotation
    writeIORef rot (rotation + 0.01)
    swapBuffers

timer :: Int -> Window -> IO ()
timer time win = do
    postRedisplay (Just win)
    addTimerCallback time (timer time win)

main :: IO ()
main = do
    initialize "glut" []
    initialDisplayMode $= [DoubleBuffered]
    (mainwin, _) <- enterGameMode
    initScreen
    rot <- newIORef 0
    displayCallback $= redraw mainwin rot
    timer 33 mainwin
    mainLoop
