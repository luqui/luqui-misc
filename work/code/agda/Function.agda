module Function where

flip : {a b c : Set} -> (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

const : {a b : Set} -> a -> b -> a
const x y = x

id : {a : Set} -> a -> a
id x = x
