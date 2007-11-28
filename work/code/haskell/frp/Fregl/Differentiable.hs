{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Differentiable where

class Differentiable d where
    type Derivative d :: *
    differentiate :: Double -> d -> d -> Derivative d
    integrate     :: Double -> Derivative d -> d -> d

instance Differentiable Double where
    type Derivative Double = Double
    differentiate dt a b = (b - a) / dt
    integrate     dt d a = a + d*dt
