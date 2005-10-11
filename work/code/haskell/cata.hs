data Rec f = In { out :: f (Rec f) }

cata :: (Functor f) => (f a -> a) -> Rec f -> a
cata f (In a) = f (fmap (cata f) a)

ana :: (Functor f) => (a -> f a) -> a -> Rec f
ana f a = In $ fmap (ana f) $ f a
