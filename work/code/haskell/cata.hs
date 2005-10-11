data Rec f = In { out :: f (Rec f) }

cata f (In a) = f (fmap (cata f) a)
