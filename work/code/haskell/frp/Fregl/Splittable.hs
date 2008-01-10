module Fregl.Splittable where

class Splittable a where
    split :: a -> (a,a)
