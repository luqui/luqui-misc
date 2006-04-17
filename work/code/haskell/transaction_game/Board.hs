{-# OPTIONS_GHC -fglasgow-exts #-}

module Board (
) where

import qualified Player
import qualified Data.Map as Map
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
	= Board { boardState :: Map.Map Vertex NodeState }
	deriving Show

emptyBoard :: Board
emptyBoard = Board { boardState = Map.empty }

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
runMove move@(Place {}) (Board board)
	| Owned { nodePlayer = p } <- getSpace (moveVertex move) board,
	  p == movePlayer move
	= Just $ Board $ Map.adjust (adjustArmy (+ moveArmy move)) (moveVertex move) board

-- Transfer requires that both 'from' and 'to' are owned by the player
-- and that 'from' has at least 'army' troops
runMove move@(Transfer {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		 <- getSpace (moveFrom move) board,
	  Owned { nodePlayer = toOwner }   <- getSpace (moveTo move) board,
	  fromOwner == movePlayer move,
	  toOwner   == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board $ (Map.adjust (adjustArmy (+ moveArmy move)) (moveTo move) .
	                  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove move@(Occupy {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy }
		 <- getSpace (moveFrom move) board,
	  Unowned <- getSpace (moveTo move) board,
	  fromOwner == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board $ (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove move@(Attack {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		<- getSpace (moveFrom move) board,
	  Owned { nodePlayer = toOwner,   nodeArmy = toArmy }   
		<- getSpace (moveTo move) board,
	  fromOwner == movePlayer move,
	  toOwner   == moveVictim move,
	  fromArmy >= moveArmy move,
	  moveArmy move > toArmy
	= Just $ Board $ (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove _ _ = Nothing

-- Note that the last move in the transaction is the first in the list!
type Transaction = [Move]

tryTransaction :: Transaction -> Board -> Maybe Board
tryTransaction ms board = foldr (=<<) (Just board) (map runMove ms)
