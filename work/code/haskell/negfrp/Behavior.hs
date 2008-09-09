{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving #-}

module Behavior where

import Control.Applicative
import Control.Compose
import Wait
import StepFun
import Fun

newtype Behavior a = Behavior { unBehavior :: (StepFun :. Fun DTime) a }
    deriving (Functor, Applicative)

untilB :: Behavior a -> Wait (Behavior a) -> Behavior a
untilB b w = Behavior . O $ (unO . unBehavior) b `untilStep` fmap (unO . unBehavior) w

timeB :: Behavior Double
timeB = Behavior . O . pure $ funF id
