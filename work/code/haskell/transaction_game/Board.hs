{-# OPTIONS_GHC -fglasgow-exts #-}

module Board (
	NodeState(..),
	Board(..),
	Move(..),
	givePlayer,
	emptyBoard,
	runMove,
	tryTransaction,
	Transaction,
	Army,
) where

import qualified Player
import qualified Data.Map as Map
import qualified Graph
import Graph (Vertex)

type Army = Int

data NodeState
	= Unowned
	| Owned { nodePlayer :: Player.Player, nodeArmy :: Army }
	deriving Show

adjustArmy :: (Army -> Army) -> NodeState -> NodeState
adjustArmy _ Unowned = error "Can't adjust unowned space without owner"
adjustArmy f s = s { nodeArmy = f (nodeArmy s) }

data Board
	= Board 
		{ boardState :: Map.Map Vertex NodeState 
		, boardGraph :: Graph.Graph }
	deriving Show

emptyBoard :: Graph.Graph -> Board
emptyBoard g = Board { boardState = Map.empty, boardGraph = g }

givePlayer :: Player.Player -> Vertex -> Board -> Board
givePlayer p v b@(Board { boardState = state }) =
	b { boardState = Map.insert v (Owned { nodePlayer = p, nodeArmy = 0 }) state }

getSpace :: Vertex -> Map.Map Vertex NodeState -> NodeState
getSpace = Map.findWithDefault Unowned


data Move
	= Place      
		{ movePlayer :: Player.Player
		, moveArmy   :: Army
		, moveVertex :: Vertex 
		}
	| Transfer   
		{ movePlayer :: Player.Player
		, moveFrom   :: Vertex
		, moveTo     :: Vertex
		, moveArmy   :: Army 
		}
	| Occupy
		{ movePlayer :: Player.Player
		, moveFrom   :: Vertex
		, moveTo     :: Vertex
		, moveArmy   :: Army
		}
	| Attack
		{ movePlayer :: Player.Player
		, moveVictim :: Player.Player
		, moveFrom   :: Vertex
		, moveTo     :: Vertex
		, moveArmy   :: Army
		}
	deriving Show

runMove :: Move -> Board -> Maybe Board
-- Place requires that the target vertex is owned by the player
runMove move@(Place {}) (Board board graph)
	| Owned { nodePlayer = p } <- getSpace (moveVertex move) board,
	  p == movePlayer move
	= Just $ Board 
		{ boardState = Map.adjust (adjustArmy (+ moveArmy move)) (moveVertex move) board
		, boardGraph = graph }

-- Transfer requires that both 'from' and 'to' are owned by the player
-- and that 'from' has at least 'army' troops
runMove move@(Transfer {}) (Board board graph)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		 <- getSpace (moveFrom move) board,
	  Owned { nodePlayer = toOwner }   <- getSpace (moveTo move) board,
	  Graph.hasEdge graph (moveFrom move, moveTo move),
	  fromOwner == movePlayer move,
	  toOwner   == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board 
		{ boardState = (Map.adjust (adjustArmy (+ moveArmy move)) (moveTo move) .
	                    Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board
		, boardGraph = graph }

runMove move@(Occupy {}) (Board board graph)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy }
		 <- getSpace (moveFrom move) board,
	  Unowned <- getSpace (moveTo move) board,
	  Graph.hasEdge graph (moveFrom move, moveTo move),
	  fromOwner == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board 
		{ boardState = (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					    Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board
		, boardGraph = graph }

runMove move@(Attack {}) (Board board graph)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		<- getSpace (moveFrom move) board,
	  Owned { nodePlayer = toOwner,   nodeArmy = toArmy }   
		<- getSpace (moveTo move) board,
	  Graph.hasEdge graph (moveFrom move, moveTo move),
	  fromOwner == movePlayer move,
	  toOwner   == moveVictim move,
	  fromArmy >= moveArmy move,
	  moveArmy move > toArmy
	= Just $ Board 
		{ boardState = (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					    Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board
		, boardGraph = graph }

runMove _ _ = Nothing

-- Note that the last move in the transaction is the first in the list!
type Transaction = [Move]

tryTransaction :: Transaction -> Board -> Maybe Board
tryTransaction ms board = foldr (=<<) (Just board) (map runMove ms)
