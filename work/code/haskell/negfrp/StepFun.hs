module StepFun 
    ( StepFun, consStep, untilStep )
where

import Wait
import Control.Applicative
import Data.Monoid

data StepFun a = StepFun a (Wait (StepFun a))

instance Functor StepFun where
    fmap f (StepFun x w) = StepFun (f x) ((fmap.fmap) f w)

instance Applicative StepFun where
    pure x = StepFun x mempty
    StepFun f fw <*> StepFun x xw = 
        StepFun (f x) (fmap elim (mappend fws xws))
        where
        fws = fmap Left fw
        xws = fmap Right xw
        elim (Left f') = f' <*> StepFun x xw
        elim (Right x') = StepFun f fw <*> x'

consStep :: a -> Wait (StepFun a) -> StepFun a
consStep = StepFun

untilStep :: StepFun a -> Wait (StepFun a) -> StepFun a
untilStep (StepFun x xw) w = StepFun x (xw `mappend` w)
