{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

import Control.Monad
import Control.Monad.Cont
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer
import Debug.Trace

data EventVal 
    = TimestepEvent Double
    | MouseClickEvent (Double,Double)
    deriving (Show)

newtype EventT r m a
    = EventT { runEventT :: 
         WriterT [EventVal -> EventT r m r] (
            ContT r (
                ReaderT ((EventVal -> EventT r m r) -> EventT r m EventVal) (
                    m
                )
            )
         ) a
      }

instance MonadTrans (EventT r) where
    lift = EventT . lift . lift . lift

instance (Monad m) => Monad (EventT r m) where
    return = EventT . return
    m >>= k = EventT $ runEventT m >>= runEventT . k

instance (Monad m) => MonadCont (EventT r m) where
    -- I don't know how anyone came up with this...
    callCC f = EventT $ callCC $ \c -> runEventT $ f $ EventT . c

instance (Monad m) => MonadWriter [EventVal -> EventT r m r] (EventT r m) where
    tell   = EventT . tell
    listen = EventT . listen . runEventT
    pass   = EventT . pass   . runEventT

instance (Monad m) => MonadReader ((EventVal -> EventT r m r) -> EventT r m EventVal) (EventT r m) where
    ask     = EventT ask
    local f = EventT . local f . runEventT


type Ev a = EventT () IO a

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
    callCC cont

waitTimestep :: Ev Double
waitTimestep = do
    e <- waitEvent
    case e of
         TimestepEvent d -> return d
         _ -> waitTimestep

waitClick :: Ev (Double,Double)
waitClick = do
    e <- waitEvent
    case e of
         MouseClickEvent pos -> return pos
         _ -> waitClick

timer :: Ev (Ev Double)
timer = timer' 0
    where
    timer' v = return v `untilB` (waitTimestep >>= timer')


testProg :: Ev ()
testProg = do
    tmr <- timer
    v <- tmr `untilB` (waitClick >> timer)
    v' <- v
    lift $ liftIO $ print v'


testEvents = [ TimestepEvent 0.1, TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1
             ]

