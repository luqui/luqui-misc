{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

module Fregl.Vector where

infixl 6 ^+^, ^-^
infixl 7 *^, ^*, ^*^, ^/

class (Num (Field v)) => Vector v where
    type Field v :: *
    zero  :: v
    (^+^) :: v -> v -> v
    (*^)  :: Field v -> v -> v
    (^*^) :: v -> v -> Field v
    
(^*) :: (Vector v) => v -> Field v -> v
(^*) = flip (*^)

(^-^) :: (Vector v) => v -> v -> v
x ^-^ y = x ^+^ (-1) *^ y

(^/) :: (Vector v, Fractional (Field v)) => v -> Field v -> v
x ^/ a = x ^* (1 / a)

norm2 :: (Vector v) => v -> Field v
norm2 v = v ^*^ v

norm :: (Vector v, Floating (Field v)) => v -> Field v
norm v = sqrt (norm2 v)

unitize :: (Vector v, Floating (Field v)) => v -> v
unitize v = v ^* recip (norm v)

projectTo :: (Vector v, Floating (Field v)) => v -> v -> v
projectTo to v = ((v ^*^ to) *^ to) ^/ norm2 to

instance Vector Double where
    type Field Double = Double
    zero = 0
    (^+^) = (+)
    (*^)  = (*)
    (^*^) = (*)

type Vec2 a = (a,a)

instance (Num a) => Vector (Vec2 a) where
    type Field (Vec2 a) = a
    zero = (0,0)
    (!x,!y) ^+^ (!x',!y') = (x+x',y+y')
    a *^ (!x,!y) = (a*x, a*y)
    (!x,!y) ^*^ (!x',!y') = x*x' + y*y'

type Vec3 a = (a,a,a)

instance (Num a) => Vector (Vec3 a) where
    type Field (Vec3 a) = a
    zero = (0,0,0)
    (!x,!y,!z) ^+^ (!x',!y',!z') = (x+x',y+y',z+z')
    a *^ (!x,!y,!z) = (a*x,a*y,a*z)
    (!x,!y,!z) ^*^ (!x',!y',!z') = x*x' + y*y' + z*z'
