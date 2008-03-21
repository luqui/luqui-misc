module ackermann where

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

A : Nat -> Nat -> Nat
A zero n = succ n
A (succ m) zero = A m (succ zero)
A (succ m) (succ n) = A m (A (succ m) n)