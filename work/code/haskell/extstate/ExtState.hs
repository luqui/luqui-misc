module ExtState 
    ( MonadExtState(..)
    , ExtStateT
    , runExtStateT
    )
where

import Data.Unique
import System.Mem.Weak
import qualified Data.IntMap as IntMap
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Unsafe.Coerce
import System.IO.Unsafe

data ExtPtr a = ExtPtr Unique

newtype UnsafeWeak = UnsafeWeak { fromUnsafeWeak :: forall a. Weak a }
newtype ExtMap = ExtMap (IntMap.IntMap [(Unique, UnsafeWeak)])

mkExtPtr :: a -> ExtMap -> IO (ExtPtr a, ExtMap)
mkExtPtr v emap = do
    k' <- newUnique
    let k = ExtPtr k'
    emap' <- setExtPtr k v emap
    return (k,emap')


setExtPtr :: ExtPtr a -> a -> ExtMap -> IO ExtMap
setExtPtr k@(ExtPtr k') v (ExtMap emap) = do
    val <- mkWeak k v Nothing
    return $ ExtMap $ IntMap.insertWith update
                              (hashUnique k')
                              [(k', UnsafeWeak (unsafeCoerce val))]
                              emap
    where
    update a [] = a
    update [a@(k,v)] (o@(k',v'):xs) 
        | k == k'   = a:xs
        | otherwise = o:update [a] xs


lookupExtPtr :: ExtMap -> ExtPtr a -> IO (Maybe a)
lookupExtPtr (ExtMap emap) (ExtPtr k') = do
    let mwv = lookup k' =<< IntMap.lookup (hashUnique k') emap
    case mwv of
        Nothing -> return Nothing
        Just (UnsafeWeak wv) -> do
            deRefWeak wv

pruneExtMap :: ExtMap -> IO ExtMap
pruneExtMap (ExtMap emap) = do
    assocs <- fmap concat $ flip mapM (IntMap.toList emap) $ \(k,vs) -> do
        vs' <- filterM (fmap isJust . deRefWeak . fromUnsafeWeak . snd) vs
        return $ if null vs'
                    then []
                    else [(k,vs')]
    return (ExtMap (IntMap.fromList assocs))


class MonadExtState p m | m -> p where
    newExtPtr   :: a -> m (p a)
    readExtPtr  :: p a -> m a
    writeExtPtr :: p a -> a -> m ()


newtype ExtStateT m a = ExtStateT (StateT ExtMap m a)
                deriving (Monad)

runExtStateT :: (Monad m) => ExtStateT m a -> m a
runExtStateT (ExtStateT s) = evalStateT s (ExtMap IntMap.empty)

instance MonadTrans ExtStateT where
    lift = ExtStateT . lift

instance (MonadIO m) => MonadIO (ExtStateT m) where
    liftIO = ExtStateT . liftIO

instance (Monad m) => MonadExtState ExtPtr (ExtStateT m) where
    newExtPtr v = ExtStateT $ do
        -- XXX need pruning
        emap <- get
        let (ptr,emap') = unsafePerformIO (mkExtPtr v emap)
        put emap'
        return ptr
    readExtPtr p = ExtStateT $ do
        emap <- get
        case unsafePerformIO (lookupExtPtr emap p) of
             Just a  -> return a
             Nothing -> error "ExtState module messed up!"
    writeExtPtr p v = ExtStateT $ do
        modify (unsafePerformIO . setExtPtr p v)
