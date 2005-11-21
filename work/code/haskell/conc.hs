import Control.Concurrent
import Control.Concurrent.MVar
import System.IO

countSeconds :: MVar Int -> IO ()
countSeconds var = do 
    threadDelay 1000000
    modifyMVar_ var (return . (+1))
    countSeconds var

time :: IO a -> IO (a, Int)
time action = do
    secondsM <- newMVar 0
    handle <- forkIO (countSeconds secondsM)
    value <- action
    killThread handle
    seconds <- readMVar secondsM
    return (value, seconds)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    (name, seconds) <- time (putStr "What's your name? " >> getLine)
    putStrLn $ "It took you " ++ show seconds ++ " seconds, " ++ name
