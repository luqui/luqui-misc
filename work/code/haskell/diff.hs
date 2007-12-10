import Data.List (find, transpose, foldl')
import Debug.Trace

data D a = D a a
    deriving (Eq,Show)

d :: D a -> a
d (D x x') = x'

numeric :: D a -> a
numeric (D x x') = x

instance Num a => Num (D a) where
    D a a' + D b b' = D (a+b) (a'+b')
    D a a' - D b b' = D (a-b) (a'-b')
    D a a' * D b b' = D (a*b) (a*b' + b*a')
    abs (D a a')    = D (abs a) (a' * signum a)
    signum (D a a') = D (signum a) 0
    fromInteger x   = D (fromInteger x) 0

deriv :: Num a => (D a -> D a) -> a -> a
deriv f x = let D _ d = f (D x 1) in d

jacob :: forall a. (Num a) => ([D a] -> [D a]) -> [a] -> [[a]]
jacob f x = map (map d . f . pdn) [0..length x-1]
    where
    pdn n = zipWith (\x' n' -> D x' (delta n n')) x [0..]
    delta i j | i == j    = 1
              | otherwise = 0

jacobF :: ([Double] -> [Double]) -> [Double] -> [[Double]]
jacobF f x  = map pdn [0..length x-1]
    where
    pdnh n h = zipWith (\x' n' -> if n' == n then x'+h else x') x [0..]
    pdn n = map (/0.1) $ f (pdnh n 0.05) ^-^ f (pdnh n (-0.05)) 
    (^-^) = zipWith (-)

inverse :: (Fractional a) => [[a]] -> [[a]]
inverse mat = sweep ([], zipWith (++) mat unit)
    where
    unit = map (take (length mat)) $ iterate (0:) (1:repeat 0)
    sweep (xss,[]) = xss
    sweep (xss,yss) = sweep (xss' ++ [ws], filter (any (/= 0)) yss')
        where
        Just (x:xs) = find ((/= 0).head) yss
        ws = map (/ x) xs
        [xss',yss'] = map (map f) [xss,yss]
        f (y:ys) = zipWith (\d e -> e - d*y) ws ys

matmul :: (Num a) => [[a]] -> [a] -> [a]
matmul a x = foldl' (zipWith (+)) (repeat 0) $ 
               zipWith (\x' -> map (*x')) x (transpose a)

fixpoint :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixpoint dist f init = 
    snd $ head $ until (\ ((a,a'):_) -> dist a a') tail (zip iterates (tail iterates))
    where
    iterates = iterate f init

integrate :: ([D Double] -> [D Double]) -> Double -> [Double] -> [Double]
integrate f h x = fixpoint dist iter x
    where
    iter z = z ^-^ (inverse (jacob g z) `matmul` map numeric (g (map constant z)))
    dist x y = sum (map (^2) $ x ^-^ y) < 0.0001
    constant = flip D 0
    (^+^) = zipWith (+)
    (^-^) = zipWith (-)
    (*^) a = map (*a)
    g z = map constant x 
            ^+^ (constant (h/2) *^ f (map constant x))
            ^+^ (constant (h/2) *^ f z)
            ^+^ (constant (-1) *^ z)

integrateF :: ([Double] -> [Double]) -> Double -> [Double] -> [Double]
integrateF f h x = fixpoint dist iter x
    where
    iter z = z ^-^ (inverse (jacobF g z) `matmul` g z)
    dist x y = sum (map (^2) $ x ^-^ y) < 0.0001
    (^+^) = zipWith (+)
    (^-^) = zipWith (-)
    (*^) a = map (*a)
    g z = x 
            ^+^ ((h/2) *^ f x)
            ^+^ ((h/2) *^ f z)
            ^+^ ((-1) *^ z)
