module Display (
	VertexMap,
	PlayerMap,
	emptyVertexMap,
	addVertex,
	emptyPlayerMap,
	addColor,
	displayBoard,
) where

import qualified Player
import qualified Graph
import qualified Data.Map as Map
import qualified Board

import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

data VertexMap 
	= VertexMap { vtxPos :: Map.Map Graph.Vertex (Double,Double) }

emptyVertexMap :: VertexMap
emptyVertexMap = VertexMap (Map.empty)

addVertex :: Graph.Vertex -> (Double,Double) -> VertexMap -> VertexMap
addVertex v p (VertexMap m) = VertexMap $ Map.insert v p m

data PlayerMap
	= PlayerMap { playerColor :: Map.Map Player.Player (GL.Color3 Double) }

emptyPlayerMap :: PlayerMap
emptyPlayerMap = PlayerMap (Map.empty)

addColor :: Player.Player -> GL.Color3 Double -> PlayerMap -> PlayerMap
addColor p c (PlayerMap m) = PlayerMap $ Map.insert p c m

rectPoints :: (Double,Double) -> (Double,Double) -> IO ()
rectPoints (x,y) (x',y') = do
	GL.vertex $ GL.Vertex2 x y
	GL.vertex $ GL.Vertex2 x' y
	GL.vertex $ GL.Vertex2 x' y'
	GL.vertex $ GL.Vertex2 x y'

drawVertex :: GL.Color3 Double -> (Double,Double) -> IO ()
drawVertex color (x,y) = do
	GL.color black
	GL.rect (GL.Vertex2 (x-0.5) (y-0.5)) (GL.Vertex2 (x+0.5) (y+0.5))
	GL.color white
	GL.renderPrimitive GL.LineLoop $ rectPoints (x-0.5, y-0.5) (x+0.5, y+0.5)
	GL.color color
	GL.renderPrimitive GL.Polygon $ rectPoints (x-0.3, y-0.3) (x+0.3, y+0.3)
	where
	white :: GL.Color3 Double
	white = GL.Color3 1 1 1
	black :: GL.Color3 Double
	black = GL.Color3 0 0 0

drawNode :: PlayerMap -> VertexMap -> Board.Board -> Graph.Vertex -> IO ()
drawNode cols vtxs board v = do
	let pos = vtxPos vtxs Map.! v 
	case Map.findWithDefault Board.Unowned v (Board.boardState board) of
		Board.Owned { Board.nodePlayer = player } 
			-> drawVertex (playerColor cols Map.! player) pos
		Board.Unowned
			-> drawVertex (GL.Color3 0 0 0) pos

drawLine :: (Double,Double) -> (Double,Double) -> IO ()
drawLine (x,y) (x',y') = do
	GL.color white
	GL.renderPrimitive GL.Lines $ do
		GL.vertex $ GL.Vertex2 x y
		GL.vertex $ GL.Vertex2 x' y'
	where
	white :: GL.Color3 Double
	white = GL.Color3 1 1 1

displayBoard :: PlayerMap -> VertexMap -> Board.Board -> IO ()
displayBoard cols vtxs board = do
	let g = Board.boardGraph board
	mapM_ (\ (u,v) -> drawLine (vtxPos vtxs Map.! u) (vtxPos vtxs Map.! v)) (Graph.edges g)
	mapM_ (drawNode cols vtxs board) (Graph.vertices g)
