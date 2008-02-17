module Bool where

data Bool : Set where
    True  : Bool
    False : Bool

if_then_else_ : { a : Set } -> Bool -> a -> a -> a
if True  then x else _ = x
if False then _ else x = x

not : Bool -> Bool
not True = False
not False = True
