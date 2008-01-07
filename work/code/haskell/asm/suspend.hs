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
    ask = Event ask
    local f = Event . local f . runEvent


type Ev a = Event () a

untilB :: Ev a -> Ev (Ev a) -> Ev (Ev a)
untilB sig ev = undefined
