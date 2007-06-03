{-# OPTIONS_GHC -fglasgow-exts #-}

module Werepoker.BidPhase
    ( bidPhase
    , bidTimer )
where

import qualified Control.Monad.STM as STM
import qualified Control.Concurrent.STM as STM
import Control.Concurrent (threadDelay)
import qualified Data.Map as Map
import qualified System.IO as IO
import qualified Control.Monad.Writer as Writer

import Werepoker.GameState
import Werepoker.Util


forMapM :: (Ord k, Monad m) => Map.Map k v -> (k -> v -> m ()) -> m ()
forMapM mp f = Map.foldWithKey (\k a m -> f k a >> m) (return ()) mp



-- Add a player to the game
commandPlayer :: (?gs :: STM.TVar GameState)
              => String -> IO ()
commandPlayer name = STM.atomically $ do
    gs <- STM.readTVar ?gs
    let players = gsPlayers gs
    let newPlayer = Player { pBids = Map.empty }
    STM.writeTVar ?gs $ gs { gsPlayers = Map.insert name newPlayer players }


-- Set a player's bid
commandBid :: (?gs :: STM.TVar GameState)
           => PlayerName -> RoleName -> Double -> IO ()
commandBid player role bid = STM.atomically $ do
    gs <- STM.readTVar ?gs
    let players = gsPlayers gs
    let myself = players Map.! player
    let myBids = pBids myself
    let reborn = myself { pBids = Map.insert role bid myBids }
    STM.writeTVar ?gs $ gs { gsPlayers = Map.insert player reborn players }


-- Send the anonymized status of the bidding
commandStatus :: (?gs :: STM.TVar GameState, ?handle :: IO.Handle) 
              => IO ()
commandStatus = do
    gs <- STM.atomically $ STM.readTVar ?gs
    time <- getTime
    -- create a map from roles to the highest bid
    let bidMap = Map.unionsWith max $ map pBids (Map.elems (gsPlayers gs))
    -- send the map back to the requesting client
    (IO.hPutStr ?handle =<<) $ Writer.execWriterT $ do
        Writer.tell "BID STATUS!\n"
        Writer.tell $ "Time since bid: " ++ show (time - gsLastBid gs) ++ "\n"
        forMapM bidMap $ \role bid -> do
            Writer.tell $ role ++ " - " ++ show bid ++ "\n"
        Writer.tell "--\n"


bidPhase :: STM.TVar GameState -> IO.Handle -> IO ()
bidPhase gs handle = do
    let ?gs = gs
        ?handle = handle
    line <- fmap init $ IO.hGetLine handle  -- we "init" this to remove the \r just before the end
    let again = bidPhase gs handle
    case words line of
        ["player", name] -> commandPlayer name                      >> again
        ["bid", name, role, bid] -> commandBid name role (read bid) >> again
        ["status"] -> commandStatus                                 >> again
        ["done"] -> return ()
        _ -> IO.hPutStrLn ?handle "INVALID!\n--"                     >> again

-- Given gamestate and a number of picoseconds
bidTimer :: STM.TVar GameState -> Integer -> IO ()
bidTimer gs delay = do
    time <- getTime
    lastbid <- STM.atomically $ fmap gsLastBid $ STM.readTVar gs
    if time - lastbid >= delay
        then notify
        else do
            let micro = fromInteger $ (delay + lastbid - time) * 10^6
            putStrLn $ "Waiting " ++ show micro ++ " usec"
            threadDelay micro
            bidTimer gs delay
    where
    notify = do
        putStrLn "Bidding over"
        handles <- STM.atomically $ fmap gsHandles $ STM.readTVar gs
        flip mapM_ handles $ \h -> do
            IO.hPutStrLn h "BIDDING OVER!\n--"
