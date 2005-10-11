data Rec f = In { out :: f (Rec f) }

cata :: (Functor f) => (f a -> a) -> Rec f -> a
cata f (In a) = f (fmap (cata f) a)

ana :: (Functor f) => (a -> f a) -> a -> Rec f
ana f a = In $ fmap (ana f) $ f a

data LF a lf = Nil | Cons a lf

instance Functor (LF a) where
    fmap f Nil = Nil
    fmap f (Cons a b) = Cons a (f b)
