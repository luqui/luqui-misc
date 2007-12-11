{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Differentiable where

class Differentiable d where
    type Diff d :: *
    integrate     :: Double -> Diff d -> d -> d

instance Differentiable Double where
    type Diff Double = Double
    integrate     dt d a = a + d*dt
