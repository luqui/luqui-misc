module Fregl.Event where

import Fregl.Suspend
import Fregl.Signal
import Control.Monad.Writer
import Control.Concurrent.STM
import Control.Applicative
import Data.Monoid

type ContLog v = Endo [v -> Event v ()]

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

-- occurs the first time the signal becomes Just
justEvent :: Signal (Maybe a) -> Event v a
justEvent sig = Event $ do
    val <- liftIO $ atomically $ readSignal sig
    case val of
         Just x -> return x
         Nothing -> do
             suspend
             runEvent $ justEvent sig

-- occurs the first time the signal becomes true
predicateEvent :: Signal Bool -> Event v ()
predicateEvent sig = justEvent (fmap toMaybe sig) >> return ()
    where
    toMaybe False = Nothing
    toMaybe True = Just ()

untilEvent :: Behavior v a -> Event v (Signal a) -> Behavior v a
untilEvent b ev = Behavior $ Event $ do
    choice <- attempt $ runEvent ev
    case choice of
         Left sig -> return sig
         Right cont -> do
             sigb <- runEvent $ bindBehavior b
             cell <- liftIO $ atomically $ newSignalCell sigb
             lift $ tell $ Endo $ (:) $ \v -> Event $ do
                 sig <- cont v
                 liftIO $ atomically $ overwriteSignalCell cell sig
             return $ cellSignal cell

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
    contAction sig conts v = do
        conts' <- forM (appEndo conts []) $ \cont -> do
            (choice, cs) <- runWriterT $ runSuspendT $ runEvent $ cont v
            case choice of
                 Left () -> return cs
                 Right cont -> return $ cs `mappend` (Endo $ (:) (Event . cont))
        val <- atomically $ readSignal sig
        return $ EventCxt val (contAction sig (mconcat conts'))
