{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

module Fregl.Vector where

import Fregl.Differentiable

infixl 6 ^+^, ^-^
infixl 7 *^, ^*, ^*^, ^/

class (Num (Field v)) => Vector v where
    type Field v :: *
    zero  :: v
    (^+^) :: v -> v -> v
    (*^)  :: Field v -> v -> v

class (Vector v) => InnerProduct v where
    (^*^) :: v -> v -> Field v
    
(^*) :: (Vector v) => v -> Field v -> v
(^*) = flip (*^)

(^-^) :: (Vector v) => v -> v -> v
x ^-^ y = x ^+^ (-1) *^ y

(^/) :: (Vector v, Fractional (Field v)) => v -> Field v -> v
x ^/ a = x ^* (1 / a)


norm2 :: (InnerProduct v) => v -> Field v
norm2 v = v ^*^ v

norm :: (InnerProduct v, Floating (Field v)) => v -> Field v
norm v = sqrt (norm2 v)

unitize :: (InnerProduct v, Floating (Field v)) => v -> v
unitize v = v ^* recip (norm v)

projectTo :: (InnerProduct v, Floating (Field v)) => v -> v -> v
projectTo to v = ((v ^*^ to) *^ to) ^/ norm2 to

instance Vector Double where
    type Field Double = Double
    zero = 0
    (^+^) = (+)
    (*^)  = (*)

instance InnerProduct Double where
    (^*^) = (*)

type Vec2 a = (a,a)

instance (Num a) => Vector (Vec2 a) where
    type Field (Vec2 a) = a
    zero = (0,0)
    (!x,!y) ^+^ (!x',!y') = (x+x',y+y')
    a *^ (!x,!y) = (a*x, a*y)

instance (Num a) => InnerProduct (Vec2 a) where
    (!x,!y) ^*^ (!x',!y') = x*x' + y*y'

cross2d :: (Num a) => Vec2 a -> Vec2 a -> a
cross2d (x,y) (x',y') = x * y' - y * x'

instance Differentiable (Vec2 Double) where
    type Diff (Vec2 Double) = Vec2 Double
    integrate     dt d a = a ^+^ (dt *^ d)

type Vec3 a = (a,a,a)

instance (Num a) => Vector (Vec3 a) where
    type Field (Vec3 a) = a
    zero = (0,0,0)
    (!x,!y,!z) ^+^ (!x',!y',!z') = (x+x',y+y',z+z')
    a *^ (!x,!y,!z) = (a*x,a*y,a*z)

instance (Num a) => InnerProduct (Vec3 a) where
    (!x,!y,!z) ^*^ (!x',!y',!z') = x*x' + y*y' + z*z'

instance Differentiable (Vec3 Double) where
    type Diff (Vec3 Double) = Vec3 Double
    integrate     dt d a = a ^+^ (dt *^ d)
