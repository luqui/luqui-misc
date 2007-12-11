{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Differentiable where

class Differentiable d where
    type Derivative d :: *
    integrate     :: Double -> Derivative d -> d -> d

instance Differentiable Double where
    type Derivative Double = Double
    integrate     dt d a = a + d*dt
