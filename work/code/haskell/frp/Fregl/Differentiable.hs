{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Differentiable where

class Differentiable d where
    type Diff d   :: *
    integrate     :: Double -> Diff d -> d -> d

    -- implement infIntegrate if your differential
    -- type supports infinitesimals
    infsIntegrate :: Diff d -> d -> d
    infsIntegrate d a = a

instance Differentiable Double where
    type Diff Double = Double
    integrate     dt d a = a + d*dt
