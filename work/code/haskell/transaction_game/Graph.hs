module Graph (
	Vertex,
	Graph,
	edges,
	successors,
	addEdge,
	hasEdge,
) where

import qualified Data.Set as Set

type Vertex = Int

data Graph = Graph { edges :: Set.Set (Vertex,Vertex) }

successors :: Graph -> Vertex -> [Vertex]
successors (Graph g) v = map snd $ filter ((v ==) . fst) $ Set.elems g

addEdge :: (Vertex,Vertex) -> Graph -> Graph
addEdge (v,w) = Graph . Set.insert (v,w) . Set.insert (w,v) . edges

hasEdge :: Graph -> (Vertex,Vertex) -> Bool
hasEdge (Graph g) e = e `Set.member` g
