{-# LANGUAGE GADTs #-}

data Prompt p a where
    Pure   :: a -> Prompt p a
    Effect :: p x -> (x -> Prompt p a) -> Prompt p a

instance Functor (Prompt p) where
    fmap f (Pure x) = Pure (f x)
    fmap f (Effect p bind) = Effect p (fmap f . bind)

bind :: (Monad m) => (a -> m b) -> (m a -> m b)
bind = flip (>>=)

instance Monad (Prompt p) where
    return = Pure
    Pure x >>= f = f x
    Effect p t >>= f = Effect p (bind f . t)
