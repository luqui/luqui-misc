module Fregl.Event where

import Fregl.Suspend
import Fregl.Signal
import Control.Monad.Writer
import Control.Concurrent.STM
import Control.Applicative

data EventVal

newtype Event a
    = Event { runEvent :: SuspendT EventVal (WriterT [EventVal -> Event ()] IO) a }

newtype Behavior a = Behavior { bindBehavior :: Event (Signal a) }

instance Functor Event where
    fmap = liftM

instance Monad Event where
    return = Event . return
    m >>= k = Event $ runEvent m >>= runEvent . k

instance Functor Behavior where
    fmap f = Behavior . fmap (fmap f) . bindBehavior

instance Applicative Behavior where
    pure = Behavior . return . constSignal 
    b <*> x = Behavior $ do
        b' <- bindBehavior b
        x' <- bindBehavior x
        return (b' <*> x')

waitEvent :: Event EventVal
waitEvent = Event suspend

untilEvent :: Behavior a -> Event (Signal a) -> Behavior a
untilEvent b ev = Behavior $ Event $ do
    choice <- attempt $ runEvent ev
    case choice of
         Left sig -> return sig
         Right cont -> do
             sigb <- runEvent $ bindBehavior b
             cell <- liftIO $ atomically $ newSignalCell sigb
             lift $ tell $ (:[]) $ \v -> Event $ do
                 sig <- cont v
                 liftIO $ atomically $ overwriteSignalCell cell sig
             return $ cellSignal cell
