module elim where

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

elim-Nat : (P : Nat -> Set) 
        -> P zero
        -> ((n : Nat) -> P n -> P (succ n))
        -> (n : Nat) -> P n
elim-Nat P zpf succpf zero = zpf
elim-Nat P zpf succpf (succ n) = succpf n (elim-Nat P zpf succpf n)


data PfAdd : Nat -> Nat -> Set where
    return : (x : Nat) -> (y : Nat) -> Nat -> PfAdd x y

call : (x : Nat) -> (y : Nat) -> PfAdd x y -> Nat
call x y (return .x .y c) = c


addP : (x : Nat) -> (y : Nat) -> PfAdd x y
addP = elim-Nat (\x -> (y : Nat) -> PfAdd x y)
                (\y -> return zero y y)
                (\x xhyp y -> return (succ x) y (succ (call x y (xhyp y))))
