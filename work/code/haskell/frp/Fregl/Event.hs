{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Event 
    ( Event
    , Behavior
    , bindBehavior
    , waitEvent
    , readSig
    , loopBehavior
    , untilEvent
    , newEventCxt
    , readEventCxt
    , nextEventCxt
    )
where

import Fregl.Suspend
import Fregl.Signal
import Control.Monad.Writer
import Control.Concurrent.STM
import Control.Applicative
import Data.Monoid
import System.Mem.Weak

newtype Update = Update (STM ())

instance Monoid Update where
    mempty = Update (return ())
    mappend (Update a) (Update b) = Update $ a >> b

data ContLog v = ContLog (Endo [v -> Event v ()]) Update

instance Monoid (ContLog v) where
    mempty = ContLog mempty mempty
    mappend (ContLog cont up) (ContLog cont' up') = 
        ContLog (cont `mappend` cont') (up `mappend` up')

writeCont :: (v -> Event v ()) -> ContLog v
writeCont f = ContLog (Endo $ (:) f) mempty

writeUpdate :: STM () -> ContLog v
writeUpdate m = ContLog mempty (Update m)


newtype Event v a
    = Event { runEvent :: SuspendT v (WriterT (ContLog v) IO) a }

newtype Behavior v a = Behavior { bindBehavior :: Event v (Signal a) }

instance Functor (Event v) where
    fmap = liftM

instance Monad (Event v) where
    return = Event . return
    m >>= k = Event $ runEvent m >>= runEvent . k

instance Functor (Behavior v) where
    fmap f = Behavior . fmap (fmap f) . bindBehavior

instance Applicative (Behavior v) where
    pure = Behavior . return . constSignal 
    b <*> x = Behavior $ do
        b' <- bindBehavior b
        x' <- bindBehavior x
        return (b' <*> x')

waitEvent :: Event v v
waitEvent = Event suspend

readSig :: Signal a -> Event v a
readSig = Event . liftIO . atomically . readSignal

untilEvent :: Behavior v a -> Event v (Signal a) -> Behavior v a
untilEvent b ev = Behavior $ Event $ do
    choice <- attempt $ runEvent ev
    case choice of
         Left sig -> return sig
         Right cont -> do
             sigb <- runEvent $ bindBehavior b
             cell <- liftIO $ atomically $ newSignalCell sigb
             let writer v = Event $ do
                 sig <- cont v
                 lift $ tell $ writeUpdate $ overwriteSignalCell cell sig
             weakWriter <- lift $ liftIO $ mkWeak cell writer Nothing
             tellWeak weakWriter
             return $ cellSignal cell


loopBehavior :: a -> (Signal a -> Behavior v a) -> Behavior v a
loopBehavior init f = Behavior $ do
    var <- Event $ liftIO $ atomically $ newTVar $ init
    let sigout = varSignal var
    sigin <- bindBehavior (f sigout)
    let updater _ = do
            val <- Event $ liftIO $ atomically $ readSignal sigin
            Event $ lift $ tell $ writeUpdate $ writeTVar var val
            waitEvent >>= updater
    weakUpdater <- Event $ lift $ liftIO $ mkWeak var updater Nothing
    Event $ tellWeak weakUpdater
    return sigout



tellWeak weakWriter = do
    lift $ tell $ writeCont $ \v -> do
        w <- Event $ liftIO $ deRefWeak weakWriter
        case w of
             Nothing -> return ()
             Just f -> f v

-- executing events:
data EventCxt v a = EventCxt a (v -> IO (EventCxt v a))

newEventCxt :: forall v a. Behavior v a -> IO (EventCxt v a)
newEventCxt b = do
    let event = bindBehavior b
    let suspend = runEvent event
    (Left sig, conts) <- runWriterT (runSuspendT suspend)
    val <- atomically $ readSignal sig
    return $ EventCxt val (contAction sig conts)
    where
    contAction :: Signal a -> ContLog v -> v -> IO (EventCxt v a)
    contAction sig contlog v = do
        -- Here it would be better if we performed updates *after*
        -- resuming, to be more responsive, but it's sufficiently
        -- ugly that I'd rather write this sentence explaining
        -- it than just do it.

        let ContLog (Endo conts) (Update updates) = contlog
        -- perform updates
        atomically updates

        -- resume continuations
        contlog' <- forM (conts []) $ \cont -> do
            (choice, cs) <- runWriterT $ runSuspendT $ runEvent $ cont v
            case choice of
                 Left () -> return cs
                 Right cont -> return $ cs `mappend` writeCont (Event . cont)
        val <- atomically $ readSignal sig
        return $ EventCxt val (contAction sig (mconcat contlog'))

readEventCxt :: EventCxt v a -> a
readEventCxt (EventCxt a _) = a

nextEventCxt :: v -> EventCxt v a -> IO (EventCxt v a)
nextEventCxt v (EventCxt _ n) = n v
