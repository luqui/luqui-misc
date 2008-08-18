module SecularFRP.Stream where

data Stream a
    = a :> Stream a

data StreamF i o
    = Write o (StreamF i o)
    | Read (i -> StreamF i o)

instance Functor Stream where
    fmap f (a :> as) = f a :> fmap f as

instance Functor (StreamF i) where
    fmap f (Write x sf) = Write (f x) (fmap f sf)
    fmap f (Read t) = Read (fmap f . t)

apply :: StreamF i o -> Stream i -> Stream o
apply (Write o sf) i = o :> apply sf i
apply (Read f) (i :> is) = apply (f i) is

(>>>) :: StreamF a b -> StreamF b c -> StreamF a c
Read f     >>> g          = Read (\i -> f i >>> g)
Write x sf >>> Read g     = sf >>> g x
f          >>> Write x sf = Write x (f >>> sf)

pure :: (a -> b) -> StreamF a b
pure f = puref
    where puref = Read (\i -> Write (f i) puref)

scan :: (a -> b -> a) -> a -> StreamF i b -> StreamF i a
scan f x0 (Write x sf) = 
    let c = f x0 x
    in Write c (scan f c sf)
