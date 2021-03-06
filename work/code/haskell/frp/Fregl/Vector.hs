{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

module Fregl.Vector where

class (Num (Field v)) => Vector v where
    type Field v :: *
    vzero :: v
    (^+^) :: v -> v -> v
    (*^)  :: Field v -> v -> v

class (Vector v) => InnerProduct v where
    (^*^) :: v -> v -> Field v

infixl 6 ^+^, ^-^
infixl 7 *^, ^*, ^*^, ^/

(^-^) :: (Vector v) => v -> v -> v
u ^-^ v = u ^+^ (-1) *^ v

(^*) :: (Vector v) => v -> Field v -> v
(^*) = flip (*^)

(^/) :: (Vector v, Fractional (Field v)) => v -> Field v -> v
v ^/ a = recip a *^ v

norm2 :: (InnerProduct v) => v -> Field v
norm2 v = v ^*^ v

norm :: (InnerProduct v, Floating (Field v)) => v -> Field v
norm = sqrt . norm2

normalize :: (InnerProduct v, Floating (Field v)) => v -> v
normalize v = v ^/ norm v

instance Vector Double where
    type Field Double = Double
    vzero = 0
    (^+^) = (+)
    (*^) = (*)

instance InnerProduct Double where
    (^*^) = (*)

type Euclid2 a = (a,a)
type Vec2 = Euclid2 Double

instance (Num a) => Vector (Euclid2 a) where
    type Field (Euclid2 a) = a
    vzero = (0,0)
    (x,y) ^+^ (x',y') = (x+x', y+y')
    a *^ (x,y) = (a*x, a*y)

instance (Num a) => InnerProduct (Euclid2 a) where
    (x,y) ^*^ (x',y') = x*x' + y*y'


type Euclid3 a = (a,a,a)
type Vec3 = Euclid3 Double

instance (Num a) => Vector (Euclid3 a) where
    type Field (Euclid3 a) = a
    vzero = (0,0,0)
    (!x,!y,!z) ^+^ (!x',!y',!z') = (x+x', y+y', z+z')
    (!a) *^ (!x,!y,!z) = (a*x, a*y, a*z)

instance (Num a) => InnerProduct (Euclid3 a) where
    (x,y,z) ^*^ (x',y',z') = x*x' + y*y' + z*z'


type Euclid4 a = (a,a,a,a)
type Vec4 = Euclid4 Double

instance (Num a) => Vector (Euclid4 a) where
    type Field (Euclid4 a) = a
    vzero = (0,0,0,0)
    (!x,!y,!z,!w) ^+^ (!x',!y',!z',!w') = (x+x', y+y', z+z', w+w')
    (!a) *^ (!x,!y,!z,!w) = (a*x, a*y, a*z, a*w)

instance (Num a) => InnerProduct (Euclid4 a) where
    (x,y,z,w) ^*^ (x',y',z',w') = x*x' + y*y' + z*z' + w*w'
