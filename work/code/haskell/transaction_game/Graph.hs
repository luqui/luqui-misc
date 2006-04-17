module Graph (
	Vertex,
	Graph,
	empty,
	edges,
	vertices,
	successors,
	addEdge,
	hasEdge,
) where

import qualified Data.Set as Set

type Vertex = Int

data Graph = Graph { graphEdges :: Set.Set (Vertex,Vertex) }
	deriving Show

empty :: Graph
empty = Graph (Set.empty)

edges :: Graph -> [(Vertex,Vertex)]
edges (Graph g) = Set.elems g

vertices :: Graph -> [Vertex]
vertices (Graph g) = Set.elems $ Set.map fst g

successors :: Graph -> Vertex -> [Vertex]
successors (Graph g) v = map snd $ filter ((v ==) . fst) $ Set.elems g

addEdge :: (Vertex,Vertex) -> Graph -> Graph
addEdge (v,w) = Graph . Set.insert (v,w) . Set.insert (w,v) . graphEdges

hasEdge :: Graph -> (Vertex,Vertex) -> Bool
hasEdge (Graph g) e = e `Set.member` g
