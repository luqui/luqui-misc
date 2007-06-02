import qualified Network
import qualified System.IO as IO
import qualified Data.Map as Map
import qualified Control.Monad.STM as STM
import qualified Control.Concurrent.STM as STM
import Control.Concurrent (forkIO)

data Role
    = Role String
    deriving (Eq, Ord)

type Bids = Map.Map Role Double

data Player
    = Player { pBids :: Bids }

data GameState
    = GameState { gsPlayers :: Map.Map String Player }

threadLoop :: STM.TVar GameState -> Network.Socket -> IO a
threadLoop gs sock = do
    (handle, _, _) <- Network.accept sock
    IO.hSetBuffering handle IO.LineBuffering
    forkIO (forever $ threadMain gs handle)
    threadLoop gs sock

forMapM :: (Ord k, Monad m) => Map.Map k v -> (k -> v -> m ()) -> m ()
forMapM mp f = Map.foldWithKey (\k v m -> f k v >> m) (return ()) mp

forever :: (Monad m) => m a -> m b
forever m = m >> forever m

modifyTVar :: STM.TVar a -> (a -> a) -> STM.STM ()
modifyTVar tv f = do
    val <- STM.readTVar tv
    STM.writeTVar tv (f val)

threadMain :: STM.TVar GameState -> IO.Handle -> IO ()
threadMain gs handle = do
    line <- fmap init $ IO.hGetLine handle
    let wds = words line
    case wds of
        ["player", name] -> STM.atomically $ do
            gs' <- STM.readTVar gs
            let players = gsPlayers gs'
            let newPlayer = Player { pBids = Map.empty }
            STM.writeTVar gs $ gs' { gsPlayers = Map.insert name newPlayer players }
        ["bid", player, role, bidS] -> STM.atomically $ do
            let bid = read bidS
            players <- fmap gsPlayers $ STM.readTVar gs
            let myself = players Map.! player
            let myBids = pBids myself
            let reborn = myself { pBids = Map.insert (Role role) bid myBids }
            modifyTVar gs $ \x -> x { gsPlayers = Map.insert player reborn players }
        ["status"] -> do
            players <- STM.atomically $ fmap gsPlayers $ STM.readTVar gs
            forMapM players $ \name player -> do
                IO.hPutStrLn handle name
                forMapM (pBids player) $ \(Role roleName) bid -> do
                    IO.hPutStrLn handle $ "    " ++ roleName ++ " = " ++ show bid
    return ()

main :: IO ()
main = do
    gs <- STM.atomically $ STM.newTVar $ GameState { gsPlayers = Map.empty }
    sock <- Network.listenOn $ Network.PortNumber 1777
    threadLoop gs sock
    Network.sClose sock
