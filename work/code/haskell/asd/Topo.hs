module Topo where

import Scheduler


data Σ = T deriving Show
type Sigma = Σ

toΣ c = if c then T else never

infixl 2 \/
infixl 3 /\
(\/),(/\) :: Σ -> Σ -> Σ
x /\ y = x `seq` y
(\/) = unamb

infix 4 ===
class Discrete t where
    (===) :: t -> t -> Σ

infix 4 =/=
class Hausdorff t where
    (=/=) :: t -> t -> Σ

class Compact t where
    forevery :: (t -> Σ) -> Σ

class Overt t where
    forsome :: (t -> Σ) -> Σ


newtype Nat = Nat Integer
    deriving (Eq,Show,Num,Ord,Real,Enum,Integral)

instance Discrete  Nat where 
    x === y = toΣ $ x == y
instance Hausdorff Nat where 
    x =/= y = toΣ $ x /= y
instance Overt     Nat where
    forsome p = foldr1 (\/) (map p [0..])
