module List where

infixr 5 _::_ _++_

open import Nat
open import Function
open import Bool

data [_] (a : Set) : Set where
    []   : [ a ]
    _::_ : a -> [ a ] -> [ a ]

{-# BUILTIN LIST [_]  #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_ #-}

foldr : {a b : Set} -> b -> (a -> b -> b) -> [ a ] -> b
foldr nilC consC []        = nilC
foldr nilC consC (x :: xs) = consC x (foldr nilC consC xs)

foldl : {a b : Set} -> b -> (b -> a -> b) -> [ a ] -> b
foldl nilC consC []        = nilC
foldl nilC consC (x :: xs) = foldl (consC nilC x) consC xs

_++_ : {a : Set} -> [ a ] -> [ a ] -> [ a ]
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {a b : Set} -> (a -> b) -> [ a ] -> [ b ]
map f = foldr [] (\x r -> f x :: r)

length : {a : Set} -> [ a ] -> Nat
length = foldr zero (const suc)

range : Nat -> Nat -> [ Nat ]
range m n = map (_+_ m) (range' (n - m) zero)
    where
    range' : Nat -> Nat -> [ Nat ]
    range' zero _    = []
    range' (suc x) y = y :: range' x (suc y)

filter : {a : Set} -> (a -> Bool) -> [ a ] -> [ a ]
filter pred [] = []
filter pred (x :: xs) = (if pred x then _::_ x else id) (filter pred xs)

all : {a : Set} -> (a -> Bool) -> [ a ] -> Bool
all pred [] = True
all pred (x :: xs) = if pred x then all pred xs else False

any : {a : Set} -> (a -> Bool) -> [ a ] -> Bool
any pred [] = False
any pred (x :: xs) = if pred x then True else any pred xs

take : {a : Set} -> Nat -> [ a ] -> [ a ]
take zero    _         = []
take (suc _) []        = []
take (suc n) (x :: xs) = x :: take n xs

drop : {a : Set} -> Nat -> [ a ] -> [ a ]
drop zero    xs        = xs
drop (suc _) []        = []
drop (suc n) (x :: xs) = drop n xs
