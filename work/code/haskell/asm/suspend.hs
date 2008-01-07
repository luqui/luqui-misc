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

newtype Event r a
    = Event { runEvent :: 
         WriterT [EventVal -> Event r r] (
            ContT r (
                ReaderT ((EventVal -> Event r r) -> Event r EventVal) (
                    IO
                )
            )
         ) a
      }

instance Monad (Event r) where
    return = Event . return
    m >>= k = Event $ runEvent m >>= runEvent . k

instance MonadCont (Event r) where
    -- I don't know how anyone came up with this...
    callCC f = Event $ callCC $ \c -> runEvent $ f $ Event . c

instance MonadWriter [EventVal -> Event r r] (Event r) where
    tell   = Event . tell
    listen = Event . listen . runEvent
    pass   = Event . pass   . runEvent

instance MonadReader ((EventVal -> Event r r) -> Event r EventVal) (Event r) where
    ask     = Event ask
    local f = Event . local f . runEvent


type Ev a = Event () a

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
    Event $ liftIO $ print v'


testEvents = [ TimestepEvent 0.1, TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1
             ]

