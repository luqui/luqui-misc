module Primes where

open import AgdaPrelude

isPrime : Nat -> Bool
isPrime n = all (\x -> mod n x /= 0) (range 2 n)

primes : Nat -> [ Nat ]
primes n = filter isPrime (range 2 n)

allPrimes : [ Nat ]
allPrimes = allPrimes' 2
    where
    allPrimes' : Nat -> [ Nat ]
    allPrimes' n = (if isPrime n then _::_ n else id) (allPrimes' (suc n))
