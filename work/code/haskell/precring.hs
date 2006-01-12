{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Ratio

{- A precedence ring is a nonempty set S with a total order <=
   and two functions: up: S->S and down: S->S such that:

   up(x)   > x
   down(x) < x
   if a > b then down(a) > b
   if a < b then up(a) < b
-}

class Ord a => PrecRing a where
    pzero :: a
    up    :: a -> a
    down  :: a -> a

instance PrecRing (Ratio Integer) where
    pzero  = 1%1
    up x   = x + 1 % (denominator x * 2)
    down x = x - 1 % (denominator x * 2)
