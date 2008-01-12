{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Event 
    ( Event
    , waitEvent
    , readSig
    , untilEvent
    , unsafeEventIO
    , newEventCxt
    , readEventCxt
    , nextEventCxt
    )
where

import Fregl.Suspend
import Fregl.Signal
import Control.Monad.Writer.Strict
import Control.Concurrent.STM
import Data.Monoid
import System.Mem.Weak
import System.Mem

newtype Update = Update (STM ())

instance Monoid Update where
    mempty = Update (return ())
    mappend (Update a) (Update b) = Update $ a >> b

data ContLog v = ContLog (Dual [v -> Event v ()]) Update

instance Monoid (ContLog v) where
    mempty = ContLog mempty mempty
    mappend (ContLog cont up) (ContLog cont' up') = 
        ContLog (cont `mappend` cont') (up `mappend` up')

writeCont :: (v -> Event v ()) -> ContLog v
writeCont f = ContLog (Dual [f]) mempty

writeUpdate :: STM () -> ContLog v
writeUpdate m = ContLog mempty (Update m)


newtype Event v a
    = Event { runEvent :: SuspendT v (WriterT (ContLog v) IO) a }

instance Functor (Event v) where
    fmap = liftM

instance Monad (Event v) where
    return = Event . return
    m >>= k = Event $ runEvent m >>= runEvent . k

instance MonadFix (Event v) where
    mfix f = Event $ mfix (runEvent . f)

waitEvent :: Event v v
waitEvent = Event suspend

readSig :: Signal a -> Event v a
readSig = Event . liftIO . atomically . readSignal

untilEvent :: Signal a -> Event v (Signal a) -> Event v (Signal a)
untilEvent sigb ev = Event $ do
    choice <- attempt $ runEvent ev
    case choice of
         Left sig -> return sig
         Right cont -> do
             cell <- liftIO $ atomically $ newSignalCell sigb
             let writer v = Event $ do
                     sig <- cont v
                     lift $ tell $ writeUpdate $ overwriteSignalCell cell sig
             weakWriter <- lift $ liftIO $ mkWeak cell writer Nothing
             tellWeak weakWriter
             return $ cellSignal cell


tellWeak weakWriter = do
    lift $ tell $ writeCont $ \v -> do
        w <- Event $ liftIO $ deRefWeak weakWriter
        case w of
             Nothing -> do
                 Event $ liftIO $ putStrLn "euthenized orphan signal"
                 return ()
             Just f -> f v

unsafeEventIO :: IO a -> Event v a
unsafeEventIO = Event . liftIO

-- executing events:
data EventCxt v a = EventCxt a (v -> IO (EventCxt v a))

newEventCxt :: forall v a. Event v (Signal a) -> IO (EventCxt v a)
newEventCxt event = do
    let susp = runEvent event
    (Left sig, conts) <- runWriterT (runSuspendT susp)
    val <- atomically $ readSignal sig
    return $ EventCxt val (contAction sig conts)
    where
    contAction :: Signal a -> ContLog v -> v -> IO (EventCxt v a)
    contAction sig contlog v = do
        -- Here it would be better if we performed updates *after*
        -- resuming, to be more responsive, but it's sufficiently
        -- ugly that I'd rather write this sentence explaining
        -- it than just do it.

        let ContLog (Dual conts) (Update updates) = contlog
        -- perform updates
        atomically updates

        -- resume continuations
        contlog' <- forM conts $ \cont -> do
            (choice, cs) <- runWriterT $ runSuspendT $ runEvent $ cont v
            case choice of
                 Left () -> return cs
                 Right cont' -> return $ cs `mappend` writeCont (Event . cont')
        val <- atomically $ readSignal sig
        return $ EventCxt val (contAction sig (mconcat contlog'))


readEventCxt :: EventCxt v a -> a
readEventCxt (EventCxt a _) = a

nextEventCxt :: v -> EventCxt v a -> IO (EventCxt v a)
nextEventCxt v (EventCxt _ n) = n v
