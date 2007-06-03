module Werepoker.GameState 
    ( Player(..)
    , GameState(..)
    , RoleName
    , PlayerName
    , Bids
    )
where

import qualified Data.Map as Map
import qualified System.IO as IO

type PlayerName = String
type RoleName = String
type Bids = Map.Map RoleName Double

data Player
    = Player { pBids :: Bids }

data GameState
    = GameState { gsPlayers :: Map.Map PlayerName Player
                , gsHandles :: [IO.Handle]
                , gsLastBid :: Integer {- seconds -} }
