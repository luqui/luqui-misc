class Zippable f where
    fzip :: f a -> f b -> f (a,b)

instance Zippable [] where
    fzip = zip

data DL a = DL [DL a]
          | DI a
    deriving Show

instance Functor DL where
    fmap f (DI x)  = DI (f x)
    fmap f (DL xs) = DL (map (fmap f) xs)

instance Zippable DL where
    fzip (DI x)  (DI y)     = DI (x, y)
    fzip xs@(DL _) (DI y)   = fmap (\x -> (x,y)) xs
    fzip (DI x) ys@(DL _)   = fmap (\y -> (x,y)) ys
    fzip (DL xs) (DL ys)    = DL (zipWith fzip xs ys)

main :: IO ()
main = print $ fmap (uncurry (+)) $ fzip (DI 3) (DL [DI 4, DI 5, DI 6])
