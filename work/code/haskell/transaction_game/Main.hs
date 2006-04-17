module Main where

import Graphics.UI.GLUT
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

main :: IO ()
main = do
	initialize "main" []
	initialDisplayMode $= [DoubleBuffered]
	initScreen
	win <- createWindow "The transaction game!"
	displayCallback $= display
	mainLoop

initScreen :: IO ()
initScreen = do
	GL.matrixMode $= GL.Projection
	GLU.ortho2D 0 16 0 12
	GL.matrixMode $= GL.Modelview 0

display :: IO ()
display = do
	GL.clear [GL.ColorBuffer]
	swapBuffers
