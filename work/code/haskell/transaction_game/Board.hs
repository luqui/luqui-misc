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

adjustArmy :: (Army -> Army) -> NodeState -> NodeState
adjustArmy _ Unowned = error "Can't adjust unowned space without owner"
adjustArmy f s = s { nodeArmy = f (nodeArmy s) }

data Board
	= Board { boardState :: Map.Map Vertex NodeState }

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

runMove :: Move -> Board -> Maybe Board
-- Place requires that the target vertex is owned by the player
runMove move@(Place {}) (Board board)
	| Owned { nodePlayer = p } <- board Map.! moveVertex move,
	  p == movePlayer move
	= Just $ Board $ Map.adjust (adjustArmy (+ moveArmy move)) (moveVertex move) board

-- Transfer requires that both 'from' and 'to' are owned by the player
-- and that 'from' has at least 'army' troops
runMove move@(Transfer {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		 <- board Map.! moveFrom move,
	  Owned { nodePlayer = toOwner }   <- board Map.! moveTo move,
	  fromOwner == movePlayer move,
	  toOwner   == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board $ (Map.adjust (adjustArmy (+ moveArmy move)) (moveTo move) .
	                  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove move@(Occupy {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy }
		 <- board Map.! moveFrom move,
	  Unowned <- board Map.! moveTo move,
	  fromOwner == movePlayer move,
	  fromArmy >= moveArmy move
	= Just $ Board $ (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove move@(Attack {}) (Board board)
	| Owned { nodePlayer = fromOwner, nodeArmy = fromArmy } 
		<- board Map.! moveFrom move,
	  Owned { nodePlayer = toOwner,   nodeArmy = toArmy }   
		<- board Map.! moveTo move,
	  fromOwner == movePlayer move,
	  toOwner   == moveVictim move,
	  fromArmy >= moveArmy move,
	  moveArmy move > toArmy
	= Just $ Board $ (Map.insert (moveTo move) (Owned { nodePlayer = movePlayer move, nodeArmy = moveArmy move }) .
					  Map.adjust (adjustArmy (+ (-moveArmy move))) (moveFrom move)) board

runMove _ _ = Nothing

type Transaction = [Move]

tryTransaction :: Transaction -> Board -> Maybe Board
tryTransaction ms board = foldr (=<<) (Just board) (map runMove ms)
