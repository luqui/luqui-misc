import Data.Maybe
import Data.Monoid

newtype Cauchy = Cauchy [Rational]

errors :: [Rational]
errors = iterate (/2) 1

fromErrors :: [(Rational,Rational)] -> [Rational]
fromErrors xs = fromErrors' errors xs
    where
    fromErrors' (e:es) ((x,dx):xs) 
        | dx <= e   = x : fromErrors' es ((x,dx):xs)
        | otherwise = fromErrors' (e:es) xs

eqTolerance :: Rational -> Cauchy -> Cauchy -> Bool
eqTolerance tol (Cauchy xs) (Cauchy ys) = 
    fromJust $ getFirst $ mconcat $
        [ First $ checkEq x y e | (x,y,e) <- zip3 xs ys errors ]
    where
    checkEq x y e
        | abs (x - y) + 2*e <= tol = Just True
        | abs (x - y) - 2*e > tol  = Just False
        | otherwise                = Nothing

approximate :: Rational -> Cauchy -> Rational
approximate r (Cauchy xs) = 
    head [ x | (x,e) <- zip xs errors, e <= r ]

instance Eq Cauchy where
    -- Will never return True; likewise /= will never return False
    Cauchy xs == Cauchy ys = 
        and [ abs (x - y) <= 2*err 
            | (x,y,err) <- zip3 xs ys errors ]

instance Ord Cauchy where
    Cauchy xs <= Cauchy ys =
        fromJust $ getFirst $ mconcat 
            [ First $ checkLE x y e | (x,y,e) <- zip3 xs ys errors ]
        where
        checkLE x y e
            | x + e <= y - e  = Just True
            | x - e > y + e   = Just False
            | otherwise       = Nothing

instance Show Cauchy where
    show _ = "<Real>"

instance Num Cauchy where
    Cauchy xs + Cauchy ys = Cauchy $ tail $ zipWith (+) xs ys
    Cauchy xs - Cauchy ys = Cauchy $ tail $ zipWith (-) xs ys
    Cauchy xs * Cauchy ys = Cauchy $ fromErrors
                [ (x*y, e*(x+y))
                | (x,y,e) <- zip3 xs ys errors ]
    negate (Cauchy xs) = Cauchy $ map negate xs
    abs (Cauchy xs) = Cauchy $ map abs xs
    signum (Cauchy xs) = 
        Cauchy $ repeat $ fromJust $ getFirst $ mconcat 
            [ First $ sigTest x e | (x,e) <- zip xs errors ]
        where
        sigTest :: Rational -> Rational -> Maybe Rational
        sigTest x e
            | x < 0 && x + e < 0 = Just (-1)
            | x > 0 && x - e > 0 = Just 1
            | otherwise          = Nothing
    fromInteger = Cauchy . repeat . fromInteger

instance Fractional Cauchy where
    Cauchy xs / Cauchy ys = Cauchy $ fromErrors
                [ (x/y, (e*y - x*e) / y^2)
                | (x,y,e) <- zip3 xs ys errors, y /= 0 ]
    fromRational = Cauchy . repeat

-- Takes a closed-upward predicate and finds the least upper bound
lubRat :: (Rational -> Bool) -> Cauchy
lubRat f = Cauchy $ fromErrors $ uncurry binarySearch $ initBounds (-1) 1
    where
    binarySearch l u
        | f m       = (m, u-m) : binarySearch m u
        | otherwise = (m, m-l) : binarySearch l m
        where m = (l+u)/2
    initBounds l u
        | not (f l) = initBounds (2*l) u
        | f u       = initBounds l (2*u)
        | otherwise = (l,u)
