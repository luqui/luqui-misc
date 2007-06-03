module Werepoker.Main (main) where

import qualified Network
import qualified System.IO as IO
import qualified Data.Map as Map
import qualified Control.Monad.STM as STM
import qualified Control.Concurrent.STM as STM
import Control.Concurrent (forkIO)

import Werepoker.GameState
import Werepoker.BidPhase
import Werepoker.Util

threadLoop :: STM.TVar GameState -> Network.Socket -> IO ()
threadLoop gs sock = do
    (handle, _, _) <- Network.accept sock
    STM.atomically $ do
        gs' <- STM.readTVar gs
        STM.writeTVar gs $ gs' { gsHandles = handle : gsHandles gs' }
    IO.hSetBuffering handle IO.LineBuffering
    forkIO $ bidPhase gs handle >> IO.hClose handle
    threadLoop gs sock

main :: IO ()
main = do
    time <- getTime
    gs <- STM.atomically $ STM.newTVar $ 
            GameState { gsPlayers  = Map.empty
                      , gsHandles  = []
                      , gsLastBid  = time }
    sock <- Network.listenOn $ Network.PortNumber 1777
    forkIO (bidTimer gs 20)
    threadLoop gs sock
    Network.sClose sock
