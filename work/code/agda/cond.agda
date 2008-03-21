module cond where

data Absurd : Set where

data Unit : Set where
    unit  : Unit

data Bool : Set where
    True  : Bool
    False : Bool

data Maybe (a : Set) : Set where
    Just    : a -> Maybe a
    Nothing : Maybe a

not : Bool -> Bool
not True = False
not False = True

Pred : Bool -> Set
Pred True  = Unit
Pred False = Absurd

if_then_else_ : {P : Bool -> Set} -> (b : Bool) -> P True -> P False -> P b
if True  then t else f = t
if False then t else f = f

{-
if_then_else_ : {a : Set} -> (b : Bool) -> ({_ : Pred b} -> a) -> ({_ : Pred (not b)} -> a) -> a
if True  then t else f = t {unit}
if False then t else f = f {unit}
-}

isJust : {a : Set} -> Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

fromJust : {a : Set} -> (x : Maybe a) -> {_ : Pred (isJust x)} -> a
fromJust (Just a) {unit} = a
fromJust Nothing  {}

-- broken?
fmap : {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
fmap f m = Just (f (fromJust m))


-- the "proper" way, though it's unclear why the above compiles
{-
fmap' : {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
fmap' f m = if (isJust m) then (\{p} -> Just (f (fromJust m {p}))) else Nothing
-}
