module Fun 
    ( Fun, funF, constF, fromF )
where

import Control.Applicative hiding (Const)

data Fun t a
    = Fun   (t -> a)
    | Const a

funF :: (t -> a) -> Fun t a
funF = Fun

constF :: a -> Fun t a
constF = Const

fromF :: Fun t a -> t -> a
fromF (Fun d) = d
fromF (Const x) = const x

instance Functor (Fun t) where
    fmap f (Fun d) = Fun (fmap f d)
    fmap f (Const x) = Const (f x)

instance Applicative (Fun t) where
    pure = constF
    Const f <*> Const x = Const (f x)
    f <*> x = Fun (fromF f <*> fromF x)

instance Monad (Fun t) where
    return = pure
    Fun m >>= f = Fun (\t -> fromF (f (m t)) t)
    Const x >>= f = f x
