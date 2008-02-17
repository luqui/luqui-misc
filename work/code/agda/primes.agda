module Primes where

open import Nat
open import List
open import Bool

isPrime : Nat -> Bool
isPrime n = all (\x -> mod n x /= 0) (range 2 n)

primes : Nat -> [ Nat ]
primes n = filter isPrime (range 2 n)
