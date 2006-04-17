module Main where

import Graphics.UI.GLUT
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU
import qualified Data.Maybe as Maybe

import qualified Board
import qualified Graph
import qualified Display

testGraph :: (Board.Board, Display.VertexMap, Display.PlayerMap)
testGraph = (board, vmap, pmap)
	where
	board = Board.givePlayer 1 1 $
			Board.givePlayer 2 4 $
			Board.emptyBoard graph
	
	graph = foldr Graph.addEdge Graph.empty edges
	edges = [(1,2),(1,3),(2,4),(3,4)]
	
	vmap  = foldr (uncurry Display.addVertex) Display.emptyVertexMap points
	points = [(1,(2,1)), (2,(2,6)), (3,(8,6)), (4,(5,10))]

	pmap  = Display.addColor 1 (GL.Color3 1 0 0) $
		    Display.addColor 2 (GL.Color3 0 0 1) $
			Display.emptyPlayerMap

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
	let (board, vmap, pmap) = testGraph
	Display.displayBoard pmap vmap board
	swapBuffers
