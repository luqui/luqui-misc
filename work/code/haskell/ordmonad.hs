import qualified Data.Set as Set
import Debug.Trace

class OrdMonad m where
    ordReturn :: Ord a => a -> m a
    ordBind :: (Ord a, Ord b) => m a -> (a -> m b) -> m b

instance OrdMonad Set.Set where
    ordReturn = Set.singleton
    s `ordBind` f = Set.fold (\v ret -> f v `Set.union` ret) Set.empty s

data AsMonad m a where
    Embed :: (Ord a) => m a -> AsMonad m a
    Return :: OrdMonad m => a -> AsMonad m a
    Bind :: OrdMonad m => AsMonad m a -> (a -> AsMonad m b) -> AsMonad m b

instance OrdMonad m => Monad (AsMonad m) where
    return = Return
    (>>=) = Bind

unEmbed :: Ord a => AsMonad m a -> m a
unEmbed (Embed m) = m
unEmbed (Return v) = ordReturn v
unEmbed (Bind (Embed m) f) = m `ordBind` (unEmbed . f)
unEmbed (Bind (Return v) f) = unEmbed (f v)
unEmbed (Bind (Bind m f) g) = unEmbed (Bind m (\x -> Bind (f x) g))

test = unEmbed $ do
    x <- Embed $ Set.fromList [1..5]
    y <- Embed $ Set.fromList [1..5]
    return (x*y)

testq = unEmbed $ do
    x <- Embed $ Set.fromList [-5..5]
    y <- return (x^2)
    z <- Embed $ Set.singleton y
    return $ trace (show z) z
