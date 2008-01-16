{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Event 
    ( Event
    , execEvent
    , sample
    , untilEvent
    , unsafeEventIO
    , eitherEvent
    , firstOfEvents
    , waitTimestep
    , waitMouseMotion
    , waitMouseOver
    , waitMouseOut
    , waitClickPos
    , waitClickName
    , waitKeyUp
    , waitKeyDown
    )
where

import Fregl.Suspend
import Fregl.Signal
import Fregl.EventVal
import Fregl.WFQueue
import Fregl.LinearSplit
import qualified Fregl.Drawing as Draw
import Control.Monad.Reader
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TChan
import System.Mem.Weak
import System.Time
import Graphics.UI.SDL.Keysym

data ThreadData
    = forall a. ThreadData { threadData   :: EventWait
                           , threadTarget :: Maybe (Weak a)
                           }

newtype Event a
    = Event { runEvent :: ReaderT ThreadData IO a }
    deriving (Functor, Monad, MonadFix)

execEvent :: TReader EventVal -> Event a -> IO a
execEvent r e = do
    runReaderT (runEvent e) (ThreadData (EventWait r) Nothing)

sample :: Signal a -> Event a
sample = Event . liftIO  . atomically . readSignal

untilEvent :: Signal a -> Event (Signal a) -> Event (Signal a)
untilEvent siga ev = Event $ do
    cell <- liftIO $ atomically $ newSignalCell siga
    weak <- liftIO $ mkWeak cell cell Nothing
    let thread = do
            sigb <- runEvent ev
            cell' <- liftIO $ deRefWeak weak
            case cell' of
                 Nothing -> return ()
                 Just cell -> 
                    liftIO $ atomically $ overwriteSignalCell cell sigb
    r <- ask
    tdata <- liftIO $ duplicate (threadData r)
    let tdval = ThreadData tdata (Just weak)
    threadid <- liftIO $ forkIO $ runReaderT thread tdval
    return $ cellSignal cell

unsafeEventIO :: IO a -> Event a
unsafeEventIO = Event . liftIO

eitherEvent :: Event a -> Event a -> Event a
eitherEvent a b = Event $ do
    result <- liftIO $ atomically $ newTVar Nothing
    r <- ask
    ThreadData rdr target <- return r
    dupa <- liftIO $ duplicate $ rdr
    dupb <- liftIO $ duplicate $ rdr
    tida <- liftIO $ forkIO $ do
        x <- runReaderT (runEvent a) (ThreadData dupa target)
        atomically $ do
            unsafeWFAssignReader (ewait rdr) (ewait dupa)
            writeTVar result (Just x)
    tidb <- liftIO $ forkIO $ do
        x <- runReaderT (runEvent b) (ThreadData dupb target)
        atomically $ do
            unsafeWFAssignReader (ewait rdr) (ewait dupb)
            writeTVar result (Just x)
    liftIO $ atomically $ do
        res <- readTVar result
        maybe retry return res

firstOfEvents :: [Event a] -> Event a
firstOfEvents [] = error "empty list"
firstOfEvents [e] = e
firstOfEvents (e:es) = eitherEvent e (firstOfEvents es)


timeDiffSec :: ClockTime -> ClockTime -> Double
timeDiffSec (TOD sec pic) (TOD sec' pic') =
    fromIntegral (sec' - sec) + pico * fromIntegral (pic' - pic)
    where
    pico = 1.0e-12

waitEvent :: Event EventVal
waitEvent = Event $ do
    runEvent checkTarget
    r <- ask
    liftIO $ atomically $ readWFReader $ ewait (threadData r)

waitHelper :: (EventVal -> Maybe a) -> Event a
waitHelper f = do
    ev <- waitEvent
    case f ev of
         Nothing -> waitHelper f
         Just x  -> return x

checkTarget :: Event ()
checkTarget = Event $ do
    ThreadData _ r <- ask
    case r of
         Nothing -> return ()
         Just w -> do
             v <- liftIO $ deRefWeak w
             case v of
                  Nothing -> liftIO (putStrLn "euthenized orphan" >> (killThread =<< myThreadId))
                  Just _  -> return ()

-- atomic events
waitTimestep :: Double -> Event Double
waitTimestep dt = Event $ do
    runEvent $ checkTarget
    pretime <- liftIO $ getClockTime
    liftIO $ threadDelay $ floor (1.0e6 * dt)
    posttime <- liftIO $ getClockTime
    return (timeDiffSec pretime posttime)

waitMouseMotion :: Event (Double,Double)
waitMouseMotion = waitHelper $ \e -> do
    MouseEvent MouseMotion pos _ <- return e
    return pos

waitMouseOver :: Draw.Name -> Event (Double,Double)
waitMouseOver name = do
    n <- Event $ liftIO $ readLinearSplit (Draw.getName name)
    waitHelper $ \e -> do
        MouseEvent MouseMotion pos names <- return e
        guard $ n `elem` names
        return pos

waitMouseOut :: Draw.Name -> Event (Double,Double)
waitMouseOut name = do
    n <- Event $ liftIO $ readLinearSplit (Draw.getName name)
    waitHelper $ \e -> do
        MouseEvent MouseMotion pos names <- return e
        guard $ not $ n `elem` names
        return pos

waitClickPos :: MouseButton -> MouseState -> Event (Double,Double)
waitClickPos but state = waitHelper $ \e -> do
    MouseEvent (MouseButton but' state') pos _ <- return e
    guard $ but == but' && state == state'
    return pos

waitClickName :: MouseButton -> MouseState -> Draw.Name -> Event (Double,Double)
waitClickName but state name = do
    n <- Event $ liftIO $ readLinearSplit (Draw.getName name)
    waitHelper $ \e -> do
        MouseEvent (MouseButton but' state') pos names <- return e
        guard $ but == but' && state == state'
        guard $ n `elem` names
        return pos

waitKeyUp :: Event Keysym
waitKeyUp = waitHelper $ \e -> do
    KeyUpEvent sym <- return e
    return sym

waitKeyDown :: Event Keysym
waitKeyDown = waitHelper $ \e -> do
    KeyDownEvent sym <- return e
    return sym
