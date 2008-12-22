module Scheduler 
    ( amb, unamb, boot, never )
where

import Control.Concurrent
import Data.Unique
import qualified Data.Map as Map
import Control.Exception
import Control.Monad (forever)
import System.IO.Unsafe (unsafePerformIO)

newtype Thread = Thread Unique

data Scheduler = Scheduler { 
    bootSched :: IO () -> IO (),
    fork :: IO () -> IO Thread,
    kill :: Thread -> IO ()
}

modMVar mv f = do
    x <- takeMVar mv
    putMVar mv (f x)

makeScheduler :: IO Scheduler
makeScheduler = do
    forkChan <- newChan
    alive <- newMVar Map.empty  -- ThreadId -> [Thread]
    umap <- newMVar Map.empty   -- Thread -> ThreadId
    
    let fork io = block $ do
            me <- myThreadId
            ident <- newUnique
            writeChan forkChan (me, io, ident)
            return $ Thread ident
            
    let kill (Thread ident) = block $ do
            umap' <- takeMVar umap
            putMVar umap $ Map.delete ident umap'
            case Map.lookup ident umap' of
                Nothing -> return ()
                Just threadid -> do
                    killThread threadid
                    alive' <- takeMVar alive
                    putMVar alive $ Map.delete threadid alive'
                    case Map.lookup threadid alive' of
                        Nothing -> return ()
                        Just subs -> mapM_ (kill . Thread) subs 

    let boot io = do
            var <- newEmptyMVar
            thr <- newEmptyMVar
            forkIO $ do
                mythread <- myThreadId
                ident <- newUnique
                modMVar umap (Map.insert ident mythread)
                modMVar alive (Map.alter (maybe (Just []) Just) mythread)
                putMVar thr $ Thread ident
                putMVar var =<< io
            takeMVar var `finally` (kill =<< takeMVar thr)

    forkIO . forever $ do
        (requester, action, ident) <- readChan forkChan
        alive' <- takeMVar alive
        if (requester `Map.member` alive') then do
            umap' <- takeMVar umap
            threadid <- forkIO action
            putMVar umap (Map.insert ident threadid umap')
            putMVar alive (Map.insert threadid [] . Map.adjust (ident:) requester $ alive')
          else do
            putMVar alive alive'

    return $ Scheduler boot fork kill

ambS :: Scheduler -> a -> a -> IO a
ambS sched x y = do
    var <- newEmptyMVar
    ta <- fork sched (putMVar var $! x)
    tb <- fork sched (putMVar var $! y)
    ret <- takeMVar var
    kill sched ta
    kill sched tb
    return ret


mainSched = unsafePerformIO makeScheduler

boot = bootSched mainSched

amb :: a -> a -> IO a
amb = ambS mainSched

unamb :: a -> a -> a
unamb x y = unsafePerformIO (amb x y)

never :: a
never = unsafePerformIO $ takeMVar =<< newEmptyMVar
