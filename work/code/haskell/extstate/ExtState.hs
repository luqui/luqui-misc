module ExtState where

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

data ExtMap = ExtMap (IntMap.IntMap [(Unique, UnsafeWeak)])

mkExtPtr :: a -> ExtMap -> IO (ExtPtr a, ExtMap)
mkExtPtr v (ExtMap emap) = do
    k' <- newUnique
    let !k = ExtPtr k'
    val <- mkWeak k v Nothing
    return (k, ExtMap (IntMap.insertWith (++) 
                              (hashUnique k') 
                              [(k', UnsafeWeak (unsafeCoerce val))] 
                              emap))


setExtPtr :: ExtPtr a -> a -> ExtMap -> IO ExtMap


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


newtype ExtState m a = ExtState (StateT ExtMap m a)
                deriving (Monad)


instance MonadExtState ExtPtr ExtState where
    newExtPtr v = ExtState $ do
        emap <- get
        let (ptr,emap') = unsafePerformIO (mkExtPtr v emap)
        put emap'
        return ptr
    readExtPtr p = ExtState $ do
        emap <- get
        case unsafePerformIO (lookupExtPtr p emap) of
             Just a  -> return a
             Nothing -> error "ExtState module messed up!"
    writeExtPtr p v = ExtState $ do
        modify (setExtPtr p v)
