module Display (
	VertexMap,
	empty,
	addVertex,
	displayGraph,
) where

import qualified Graph
import qualified Data.Map as Map

import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU

data VertexMap 
	= VertexMap { vtxPos :: Map.Map Graph.Vertex (Double,Double) }

empty :: VertexMap
empty = VertexMap (Map.empty)

addVertex :: Graph.Vertex -> (Double,Double) -> VertexMap -> VertexMap
addVertex v p (VertexMap m) = VertexMap $ Map.insert v p m

drawVertex :: (Double,Double) -> IO ()
drawVertex (x,y) = do
	GL.color white
	GL.rect (GL.Vertex2 (x-0.5) (y-0.5)) (GL.Vertex2 (x+0.5) (y+0.5))
	where
	white :: GL.Color3 Double
	white = GL.Color3 1 1 1

drawLine :: (Double,Double) -> (Double,Double) -> IO ()
drawLine (x,y) (x',y') =
	GL.renderPrimitive GL.Lines $ do
		GL.vertex $ GL.Vertex2 x y
		GL.vertex $ GL.Vertex2 x' y'

displayGraph :: VertexMap -> Graph.Graph -> IO ()
displayGraph (VertexMap vtxs) g = do
	mapM_ (drawVertex . (vtxs Map.!)) (Graph.vertices g)
	mapM_ (\ (u,v) -> drawLine (vtxs Map.! u) (vtxs Map.! v)) (Graph.edges g)
