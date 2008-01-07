{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

import Control.Monad
import Control.Monad.Cont
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Concurrent.STM
import Debug.Trace

newtype EventT e r m a
    = EventT { runEventT :: 
         WriterT [e -> EventT e r m r] (
            ContT r (
                ReaderT ((e -> EventT e r m r) -> EventT e r m e) (
                    m
                )
            )
         ) a
      }

instance MonadTrans (EventT e r) where
    lift = EventT . lift . lift . lift

instance (Monad m) => Monad (EventT e r m) where
    return = EventT . return
    m >>= k = EventT $ runEventT m >>= runEventT . k

instance (Monad m) => MonadCont (EventT e r m) where
    -- I don't know how anyone came up with this...
    callCC f = EventT $ callCC $ \c -> runEventT $ f $ EventT . c

instance (Monad m) => MonadWriter [e -> EventT e r m r] (EventT e r m) where
    tell   = EventT . tell
    listen = EventT . listen . runEventT
    pass   = EventT . pass   . runEventT

instance (Monad m) => MonadReader ((e -> EventT e r m r) -> EventT e r m e) (EventT e r m) where
    ask     = EventT ask
    local f = EventT . local f . runEventT

data EventVal 
    = TimestepEvent Double
    | MouseClickEvent (Double,Double)
    deriving (Show)

type Ev a = EventT EventVal () IO a

untilB :: Ev a -> Ev (Ev a) -> Ev (Ev a)
untilB sig ev = do
    r <- callCC $ \cont -> do
        local (const (cont . Left)) $ do
            liftM Right ev
    case r of
         Left susp -> tell [susp] >> return sig
         Right e' -> return e'

waitEvent :: Ev EventVal
waitEvent = do
    cont <- ask
    r <- callCC cont
    return r

waitTimestep :: Ev Double
waitTimestep = do
    e <- waitEvent
    lift $ liftIO $ putStrLn "timestep"
    case e of
         TimestepEvent d -> return d
         _ -> waitTimestep

waitClick :: Ev (Double,Double)
waitClick = do
    e <- waitEvent
    lift $ liftIO $ putStrLn "click"
    case e of
         MouseClickEvent pos -> return pos
         _ -> waitClick

timer :: Ev (Ev Double)
timer = timer' 0
    where
    timer' v = return v `untilB` (waitTimestep >>= timer' . (v+))


testProg :: Ev ()
testProg = do
    tmr <- timer
    v <- tmr `untilB` (waitClick >> timer)
    v' <- v
    lift $ liftIO $ print v'

mainGame :: TVar [EventVal] -> TVar Bool -> Ev () -> Ev ()
mainGame hack hack2 m = do
    ev:evs <- atom $ readTVar hack
    atom $ writeTVar hack evs
    atom $ writeTVar hack2 True
    lift $ liftIO $ putStrLn $ "-- " ++ show ev ++ " --"
    beef <- atom $ readTVar hack2
    ((), suspensions) <- listen m
    beef <- atom $ readTVar hack2
    when beef $ do
        atom $ writeTVar hack2 False
        mapM_ (\s -> lift (liftIO (putStrLn "boobs")) >> s ev) suspensions
    mainGame hack hack2 m
    
    where
    atom :: STM a -> Ev a
    atom x = lift $ liftIO $ atomically x


testEvents = [ TimestepEvent 0.1, TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1
             ]

runMainGame :: [EventVal] -> IO ()
runMainGame evs = do
    suspvar <- atomically $ newTVar False
    evvar <- atomically $ newTVar evs
    let writer = runEventT $ mainGame evvar suspvar testProg
        cont   = runWriterT writer
        reader = runContT cont (const $ return ())
        io     = runReaderT reader $ error "no suspension context"
    io


main = do
    runMainGame testEvents
