{-# OPTIONS_GHC -fglasgow-exts #-}

module FRP.Vector where

infixl 6 ^+^, ^-^
infixl 7 *^, ^*, ^*^

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

norm2 :: (Vector v) => v -> Field v
norm2 v = v ^*^ v

norm :: (Vector v, Floating (Field v)) => v -> Field v
norm v = sqrt (norm2 v)

unitize :: (Vector v, Floating (Field v)) => v -> v
unitize v = v ^* recip (norm v)

newtype Scalar a = Scalar { fromScalar :: a }

instance (Num a) => Vector (Scalar a) where
    type Field (Scalar a) = a
    zero = Scalar 0
    Scalar x ^+^ Scalar y = Scalar (x+y)
    x *^ Scalar y = Scalar (x*y)
    Scalar x ^*^ Scalar y = x*y

type Vec2 a = (a,a)

instance (Num a) => Vector (Vec2 a) where
    type Field (Vec2 a) = a
    zero = (0,0)
    (x,y) ^+^ (x',y') = (x+x',y+y')
    a *^ (x,y) = (a*x, a*y)
    (x,y) ^*^ (x',y') = x*x' + y*y'
