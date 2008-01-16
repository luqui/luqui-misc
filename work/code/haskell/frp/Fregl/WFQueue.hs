module Fregl.WFQueue 
    ( TWriter
    , TFollower
    , TReader
    , newWFQueue
    , writeWFQueue
    , readWFQueue
    , makeWFReader
    , readWFReader
    , dupWFReader
    , unsafeWFAssignReader
    )
where

import Control.Concurrent.STM
import Control.Concurrent.STM.TVar

newtype TWriter a = TWriter (TVar (TFollower a))
newtype TFollower a = TFollower (TVar (Maybe (a, TFollower a)))
newtype TReader a = TReader (TVar (TFollower a))

newWFQueue :: STM (TWriter a, TFollower a)
newWFQueue = do
    follower <- fmap TFollower $ newTVar Nothing
    writer <- fmap TWriter $ newTVar follower
    return (writer, follower)

writeWFQueue :: TWriter a -> a -> STM ()
writeWFQueue (TWriter v) x = do
    TFollower curCell <- readTVar v
    nextCell <- fmap TFollower $ newTVar Nothing
    writeTVar curCell (Just (x, nextCell))
    writeTVar v nextCell

readWFQueue :: TFollower a -> STM (a, TFollower a)
readWFQueue (TFollower v) = do
    cell <- readTVar v
    case cell of
         Nothing -> retry
         Just x -> return x

makeWFReader :: TFollower a -> STM (TReader a)
makeWFReader = fmap TReader . newTVar

readWFReader :: TReader a -> STM a
readWFReader (TReader v) = do
    follower <- readTVar v
    (x,next) <- readWFQueue follower
    writeTVar v next
    return x

dupWFReader :: TReader a -> STM (TReader a)
dupWFReader (TReader v) = do
    follower <- readTVar v
    makeWFReader follower

unsafeWFAssignReader :: TReader a -> TReader a -> STM ()
unsafeWFAssignReader (TReader old) (TReader new) = do
    writeTVar old =<< readTVar new
