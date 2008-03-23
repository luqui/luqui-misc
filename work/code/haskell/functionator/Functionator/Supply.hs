module Functionator.Supply where

import Control.Monad.State

newtype Supply a = Supply (State Int a)
    deriving (Functor, Monad)

runSupply (Supply m) i0 = evalState m i0

alloc :: Supply Int
alloc = Supply $ do
    ret <- get
    put $! ret+1
    return ret
