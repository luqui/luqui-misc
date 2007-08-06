{-# OPTIONS_GHC -fglasgow-exts #-}

import Control.Monad.State

data Accessor s a = 
    Accessor { getVal :: s -> a
             , setVal :: a -> s -> s
             }
             
(@.) :: Accessor b c -> Accessor a b -> Accessor a c
(@.) f g = 
    Accessor { getVal = getVal f . getVal g
             , setVal = \c a -> setVal g (setVal f c (getVal g a)) a
             }

getA :: MonadState s m => Accessor s a -> m a
getA acc = get >>= (return . getVal acc)

putA :: MonadState s m => Accessor s a -> a -> m ()
putA acc x = get >>= put . setVal acc x

modA :: MonadState s m => Accessor s a -> (a -> a) -> m ()
modA acc f = do
    getA acc >>= (return . f) >>= putA acc

at :: Int -> Accessor [a] a
at n = Accessor (!! n) (\x a -> take n a ++ [x] ++ drop (n+1) a)

data Baz =
    Baz { baz_ :: Int }
    deriving Show

baz :: Accessor Baz Int
baz = Accessor baz_ (\x s -> s { baz_ = x })

data Bar =
    Bar { bar_ :: [Baz] }
    deriving Show

bar :: Accessor Bar [Baz]
bar = Accessor bar_ (\x s -> s { bar_ = x })

data Foo =
    Foo { foo_ :: Bar }
    deriving Show

foo :: Accessor Foo Bar
foo = Accessor foo_ (\x s -> s { foo_ = x })


main :: IO ()
main = flip evalStateT (Foo (Bar [Baz 1, Baz 2])) $ do
    liftIO . print =<< getA (bar @. foo)
    putA (baz @. at 2 @. bar @. foo) 42
    liftIO . print =<< getA (bar @. foo)
