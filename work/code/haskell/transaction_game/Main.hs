module Main where

import Graphics.UI.GLUT
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

import qualified Graph
import qualified Display

testGraph :: (Graph.Graph, Display.VertexMap)
testGraph = (graph, vmap)
	where
	graph = foldr Graph.addEdge Graph.empty edges
	edges = [(1,2),(1,3),(2,4),(3,4)]
	vmap  = foldr (uncurry Display.addVertex) Display.empty points
	points = [(1,(2,1)), (2,(2,6)), (3,(8,6)), (4,(5,10))]

main :: IO ()
main = do
	initialize "main" []
	initialDisplayMode $= [DoubleBuffered]
	win <- createWindow "The transaction game!"
	initScreen
	displayCallback $= display
	mainLoop

initScreen :: IO ()
initScreen = do
	GL.matrixMode $= GL.Projection
	GL.loadIdentity
	GLU.ortho2D 0 16 0 12
	GL.matrixMode $= GL.Modelview 0
	GL.loadIdentity

display :: IO ()
display = do
	GL.clear [GL.ColorBuffer]
	let (graph, vmap) = testGraph
	Display.displayGraph vmap graph
	swapBuffers
