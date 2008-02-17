module Nat where

open import Function
open import Bool

data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat -> Nat -> Nat
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

subtract : Nat -> Nat -> Nat
subtract zero n = n
subtract m zero = zero
subtract (suc m) (suc n) = subtract m n

_-_ : Nat -> Nat -> Nat
_-_ = flip subtract

{-# BUILTIN NATMINUS _-_ #-}

_*_ : Nat -> Nat -> Nat
zero  * n = zero
suc m * n = (m * n) + n

div : Nat -> Nat -> Nat
div a zero    = zero        -- XXX runtime error?
div a (suc b) = div' a b zero
    where
    div' : Nat -> Nat -> Nat -> Nat
    div' zero _ accum          = accum
    div' (suc n) zero accum    = div' n b (suc accum)
    div' (suc n) (suc m) accum = div' n m accum

mod : Nat -> Nat -> Nat
mod a zero    = zero       -- XXx runtime error!
mod a (suc b) = mod' a b a
    where
    mod' : Nat -> Nat -> Nat -> Nat
    mod' zero _ accum          = accum
    mod' (suc n) zero accum    = mod' n b n
    mod' (suc n) (suc m) accum = mod' n m accum

_==_ : Nat -> Nat -> Bool
zero    == zero    = True
zero    == (suc _) = False
(suc _) == zero    = False
(suc a) == (suc b) = a == b

_/=_ : Nat -> Nat -> Bool
a /= b = not (a == b)
