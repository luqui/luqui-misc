module HalfRef 
    ( LeftHalf
    , RightHalf
    , makeHalfRef
    , getHalfRef
    )
where

import System.IO.Unsafe
import Data.Unique
import System.Mem.Weak
import Data.IORef

data LeftHalf a  = LeftHalf (IORef (Maybe (Unique,a)))
data RightHalf a = RightHalf (IORef (Maybe (Unique,a)))

makeHalfRef :: a -> IO (LeftHalf a, RightHalf a)
makeHalfRef v = do
    unique <- newUnique
    cell <- newIORef $ Just (unique,v)

    let finalizer = writeIORef cell Nothing

    let k1 = LeftHalf cell
    addFinalizer k1 finalizer

    let k2 = RightHalf cell
    addFinalizer k2 finalizer

    return (k1,k2)

getHalfRef :: LeftHalf a -> RightHalf a -> Maybe a
getHalfRef (LeftHalf k1) (RightHalf k2) = unsafePerformIO $ do
    v1 <- readIORef k1
    v2 <- readIORef k2
    return $ case (v1,v2) of
        (Just (u1,v), Just (u2,_))
            | u1 == u2  -> Just v
        _ -> Nothing
