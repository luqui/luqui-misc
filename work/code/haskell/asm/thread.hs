{-# OPTIONS_GHC -fglasgow-exts #-}

import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TChan
import Control.Monad.Reader
import Control.Monad
import Control.Applicative

type Ev = ReaderT (TChan EventVal) IO

data SigVal a
    = SigEarly (Signal a)
    | SigLate (Signal a)

data Signal :: * -> * where
    SigConst :: a -> Signal a
    SigMap   :: (a -> b) -> Signal a -> Signal b
    SigApply :: Signal (a -> b) -> Signal a -> Signal b
    SigCell  :: TVar (SigVal a) -> Signal a

newtype Behavior a = Behavior { runBehavior :: Ev (Signal a) }

data EventVal
    = TimestepEvent Double
    | MouseClickEvent (Double,Double)
    deriving Show

instance Functor Signal where
    fmap f (SigConst a) = SigConst (f a)
    fmap f (SigMap f' sig) = SigMap (f . f') sig
    fmap f sig = SigMap f sig

instance Applicative Signal where
    pure = SigConst
    f <*> x = SigApply f x

instance Functor Behavior where
    fmap f = Behavior . fmap (fmap f) . runBehavior

readSignal :: Signal a -> Ev a
readSignal sig = liftIO $ atomically $ liftM fst $ readSignal' sig
    where
    readSignal' :: Signal a -> STM (a, Maybe (Signal a))
    readSignal' s@(SigConst a) = return (a, Nothing)
    readSignal' (SigMap f sig) = do
        (v, repl) <- readSignal' sig
        return (f v, fmap (SigMap f) repl)
    readSignal' (SigApply f a) = do
        (f', replf) <- readSignal' f
        (a', repla) <- readSignal' a
        let ret = f' a'
        case (replf, repla) of
             (Nothing, Nothing) -> return (ret, Nothing)
             (Just f, Nothing)  -> return (ret, Just $ SigApply f a)
             (Nothing, Just a)  -> return (ret, Just $ SigApply f a)
             (Just f, Just a)   -> return (ret, Just $ SigApply f a)
    -- A signal s = SigCell <SigLate s'> will never change again and therefore
    -- s is equivalent to s'.  This function implements a mutable reduction
    -- thereof.
    readSignal' (SigCell cell) = do
        val <- readTVar cell
        case val of
             SigEarly sig -> do
                 (v, repl) <- readSignal' sig
                 case repl of
                      Nothing -> return ()
                      Just c -> writeTVar cell (SigEarly c)
                 return (v, Nothing)
             SigLate sig -> do
                 (v, repl) <- readSignal' sig
                 case repl of
                      Nothing -> return ()
                      Just c -> writeTVar cell (SigEarly c)
                 return (v, Just sig)


constB :: a -> Behavior a
constB a = Behavior $ return $ SigConst a

untilB :: Behavior a -> Ev (Signal a) -> Behavior a
untilB b ev = Behavior $ do
    b' <- runBehavior b
    cell <- liftIO $ atomically $ newTVar $ SigEarly b'
    chan <- ask
    newChan <- liftIO $ atomically $ dupTChan chan
    let action = do
        sig' <- ev
        liftIO $ atomically $ writeTVar cell (SigLate sig')
    liftIO $ forkIO $ runReaderT action newChan
    return $ SigCell cell

waitEvent :: Ev EventVal
waitEvent = do
    ch <- ask
    liftIO $ atomically $ readTChan ch

waitTimestep :: Ev Double
waitTimestep = do
    e <- waitEvent
    case e of
         TimestepEvent dt -> return dt
         _ -> waitTimestep

waitClick :: Ev (Double,Double)
waitClick = do
    e <- waitEvent
    case e of
         MouseClickEvent pos -> return pos
         _ -> waitClick

time :: Double -> Behavior Double
time init = constB init `untilB` (waitTimestep >>= runBehavior . time . (init+))

rising :: Behavior Double
rising = time 0 `untilB` (waitClick >> runBehavior rising)

testProg :: Ev (Signal Double)
testProg = runBehavior rising

testEvents = [ TimestepEvent 0.1, TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1, TimestepEvent 0.1
             , MouseClickEvent (0,0)
             , TimestepEvent 0.1
             ]

main = do
    chan <- atomically $ newTChan
    sig <- runReaderT testProg chan
    doStep chan sig testEvents
    where
    doStep _ _ [] = return ()
    doStep chan sig (e:es) = do
        v <- runReaderT (readSignal sig) undefined
        print v
        print e
        atomically $ writeTChan chan e
        getLine
        doStep chan sig es
