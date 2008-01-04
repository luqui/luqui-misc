{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.FMonad
    ( FMonad

    , MagicList, MagicListWriter
    , newMagicList, writeMagicList, readMagicList
    )
where

import Control.Monad.Identity
import Control.Monad.Fix
import Control.Concurrent.STM

-- FMonad, the Fregl monad.
-- Encapsulates non-blocking operations and magic lists.

newtype FMonad a = FMonad { runFMonad :: IO a }
    deriving (Functor, Monad, MonadFix)

-- MagicList and MagicListWriters come in pairs; a MagicList
-- is immutable, just a pointer into a list.  MagicListWriter
-- always points to the end of the respective list to write
-- to it.

newtype MagicList a
    = MagicList (TVar (Maybe (a, MagicList a)))

newtype MagicListWriter a 
    = MagicListWriter (TVar (MagicList a))

newMagicList :: FMonad (MagicListWriter a, MagicList a)
newMagicList = FMonad $ atomically $ do
    tv <- newTVar Nothing
    let list = MagicList tv
    writer <- newTVar list
    return (MagicListWriter writer, list)


writeMagicList :: MagicListWriter a -> a -> FMonad ()
writeMagicList (MagicListWriter writer) v = FMonad $ atomically $ do
    MagicList tv <- readTVar writer
    Nothing <- readTVar tv -- sanity check
    tail <- fmap MagicList $ newTVar Nothing
    writeTVar tv (Just (v, tail))
    writeTVar writer tail


readMagicList :: MagicList a -> FMonad (Maybe (a, MagicList a))
readMagicList (MagicList tv) = FMonad $ atomically $ do
    readTVar tv
