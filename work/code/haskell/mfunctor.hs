{-# OPTIONS_GHC -fglasgow-exts #-}

data MFunctor a
    = forall f. Functor f => MF (f a)
    | MI a

instance Functor MFunctor where
    fmap f (MF a) = MF (fmap f a)
    fmap f (MI a) = MI (f a)


