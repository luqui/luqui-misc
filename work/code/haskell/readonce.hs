import Data.IORef
import Control.Monad
import System.IO

data ReadOnce a = ReadOnce (IORef (Maybe a))

makeReadOnce :: a -> IO (ReadOnce a)
makeReadOnce val = do
    ref <- newIORef $ Just val
    return (ReadOnce ref)

readOnce :: ReadOnce a -> IO (Maybe a)
readOnce (ReadOnce var) = do
    ans <- readIORef var
    writeIORef var Nothing
    return ans


receiver :: ReadOnce String -> IO ()
receiver locked = do
    msg <- readOnce locked
    putStrLn $ maybe "I didn't get your message -- there was a snoop!"
                     (\str -> "Ahh, you said \"" ++ str ++ "\"")
                     msg

insecure :: ReadOnce String -> (ReadOnce String -> IO ()) -> IO ()
insecure msg rcvr = do
    putStr "A message is being transferred, care to peek (y/n)? "
    resp <- getLine
    when (resp == "y") $ do 
        msg <- readOnce msg
        putStrLn $ maybe "There was no message to be found"
                         (\str -> "(whisper) The message was \"" ++ str ++ "\"")
                         msg
    rcvr msg

sender :: String -> IO ()
sender str = do
    msg <- makeReadOnce str
    insecure msg receiver

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    sender "I like Baseball!"
