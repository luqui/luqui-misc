module Functionator.Supply where

import Control.Monad.State

newtype Supply a = Supply (State Int a)
    deriving (Functor, Monad)

alloc :: Supply Int
alloc = Supply $ do
    ret <- get
    put $! ret+1
    return ret
