module codata where

-- Prelude, stuff that every program ought to have.
module Prelude where

    data Unit : Set where
        unit : Unit

    data Nat : Set where
        zero : Nat
        suc  : Nat -> Nat

    {-# BUILTIN NATURAL Nat #-}
    {-# BUILTIN ZERO zero #-}
    {-# BUILTIN SUC suc #-}

    data Pair (a b : Set) : Set where
        mkpair : a -> b -> Pair a b

    infixr 1 _∷_
    data List (a : Set) : Set where
        []   : List a
        _∷_  : a -> List a -> List a

    fst : {a b : Set} -> Pair a b -> a
    fst (mkpair x y) = x

    snd : {a b : Set} -> Pair a b -> b
    snd (mkpair x y) = y

    add : Nat -> Nat -> Nat
    add zero    n = n
    add (suc m) n = suc (add m n)

    infixl 5 _***_
    _***_ : {a b c d : Set} -> (a -> c) -> (b -> d) -> Pair a b -> Pair c d
    (f *** g) (mkpair a b) = mkpair (f a) (g b)

    infixl 1 _∘_

    _∘_ : {a b c : Set} -> (b -> c) -> (a -> b) -> (a -> c)
    (f ∘ g) x = f (g x)

    id : {a : Set} -> a -> a
    id x = x

-- Stream a is isomorphic to a function Nat -> a .  This implementation
-- of stream simply encodes itself as that isomorphism.  Were this a
-- real language, this would be an inefficient way to do it.
module StreamNF where
    open Prelude

    data Stream (a : Set) : Set where
        stream : (Nat -> a) -> Stream a

    map : {a b : Set} -> (a -> b) -> Stream a -> Stream b
    map f (stream s) = stream (f ∘ s)

    -- Coalgebraic projections.
    projHead : {a : Set} -> Stream a -> a
    projHead (stream s) = s zero

    projTail : {a : Set} -> Stream a -> Stream a
    projTail (stream s) = stream (s ∘ suc)

    -- A composition of total functions gives a total coalgebra,
    -- as witnessed by this function.
    unfold : {a b : Set} -> (b -> Pair a b) -> b -> Stream a
    unfold {a} {b} bf x = stream (inf x)
        where
        inf : b -> Nat -> a
        inf x' zero    = fst (bf x')
        inf x' (suc n) = inf (snd (bf x')) n

-- In this module we encode a stream as its unfold.  This is the
-- dual to the well-known technique of encoding a list as its
-- fold:
--   data List (a : Set) : Set where
--       fold : ({b : Set} -> (a -> b -> b) -> b -> b) -> List a
-- Notice the similarity.  It is deep and beautiful.
module StreamUnfold where
    open Prelude

    data Stream (a : Set) : Set1 where
        unfold : {b : Set} -> (b -> Pair a b) -> b -> Stream a
    
    projHead : {a : Set} -> Stream a -> a
    projHead (unfold bf i) = fst (bf i)

    projTail : {a : Set} -> Stream a -> Stream a
    projTail (unfold bf i) = unfold bf (snd (bf i))
    
    -- It is tempting to write map as follows:
    --   map f = unfold (\s -> mkpair (f (projHead s')) (projTail s'))
    -- Unfortunately, Stream a : Set1, so it doesn't fit into an
    -- argument of unfold.  No amount of magic will let it fit.  There
    -- has got to be a good reason for this.  But we can work on 
    -- the generator explicitly.
    map : {a b : Set} -> (a -> b) -> Stream a -> Stream b
    map f (unfold bf i) = unfold (\b -> (f *** id) (bf b)) i

    -- See, you can still do a lot of interesting stuff without
    -- a Turing-complete language.  This is a scan over infinitely
    -- long streams!  Doesn't sound like something that a decidable
    -- language would be able to express.
    scan : {a b : Set} -> (b -> a -> b) -> b -> Stream a -> Stream b
    scan {a} {b} f i (unfold {genT} bf i') = unfold unfolder (mkpair i i')
        where
        unfolder : Pair b genT -> Pair b (Pair b genT)
        unfolder (mkpair accum gen) = 
            let bfgen = bf gen
                inp   = fst bfgen
                gen'  = snd bfgen
                newVal = f accum inp
            in mkpair newVal (mkpair newVal gen')

    -- Convenience for inspection.
    take : {a : Set} -> Nat -> Stream a -> List a
    take zero    _ = []
    take (suc n) s = projHead s ∷ take n (projTail s)

open Prelude
open StreamUnfold
