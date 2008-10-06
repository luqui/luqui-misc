module At where

import Control.Applicative
import Control.Monad.ST.Lazy
import Control.Arrow hiding (pure)
import Temporal.DynAction
import Control.Monad.Fix

type TimeRep = Double

newtype At t a = At (DynAction (ST t) TimeRep a)
    deriving (Functor,Applicative,Monad,MonadFix)
