module At where

import Control.Applicative
import Control.Monad.ST.Lazy
import Control.Arrow hiding (pure)
import Temporal.DynAction
import Control.Monad.Fix
import System.IO.Unsafe (unsafePerformIO)
import qualified Temporal.IVar as IVar

type TimeRep = Double

newtype Time t = Time (IVar.Reader TimeRep)

newtype At t a = At { runAt :: DynAction (ST t) TimeRep a }
    deriving (Functor,Applicative,Monad,MonadFix)

data t :< t' = FakeLT

switch :: Time t' -> At t (Either (t :< t') (t' :< t))
switch (Time v) = At self
    where
    self = mkDynAction $ \t -> return $
        case unsafePerformIO $ IVar.nonblocking v of
            Nothing             -> (Left FakeLT, self)
            Just t' | t < t'    -> (Left FakeLT, self)
                    | otherwise -> (Right FakeLT, return (Right FakeLT))

now :: At t (Time t)
now = At self
    where
    self = mkDynAction $ \t -> return (Time (return t), self)
