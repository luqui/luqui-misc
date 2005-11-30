{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.List
import Debug.Trace

data Poly a = Poly [a]

instance (Fractional a) => Show (Poly a) where
    show p@(Poly xs) = 
        if p == 0 then "0" else
            concat $ intersperse " + " $ 
                concatMap (uncurry showCoef) (zip [0..] xs)
        where
        showCoef idx x =
            if x == 0 
                then []
                else case idx of
                    0 -> [show x]
                    1 -> [show x ++ " x"]
                    n -> [show x ++ " x^" ++ show n]

instance (Fractional a, Eq a) => Eq (Poly a) where
    Poly xs == Poly ys =
        if length xs >= length ys 
            then and $ zipWith (==) xs (ys ++ replicate (length xs - length ys) 0)
            else Poly ys == Poly xs

canonicalize :: (Fractional a) => [a] -> [a]
canonicalize []     = []
canonicalize (x:xs) = 
    let canon = canonicalize xs in
        if canon == [] && x == 0
            then []
            else x:canon

poly :: Fractional a => [a] -> Poly a
poly = Poly . canonicalize

polyDrop :: ([a] -> [a]) -> Poly a -> Poly a
polyDrop f (Poly xs) = Poly (f xs)

instance (Fractional a) => Num (Poly a) where
    Poly xs + Poly ys = 
        if length xs >= length ys
            then Poly $ canonicalize $ 
                    zipWith (+) xs (ys ++ replicate (length xs - length ys) 0)
            else Poly ys + Poly xs
    negate (Poly xs)  = Poly $ map negate xs

    Poly xs * Poly ys = polyDrop canonicalize $ sum $
        map (\ (idx,f) -> Poly (replicate idx 0 ++ map (f*) ys)) $
            zip [0..] xs

    abs (Poly xs) = 
        let c = last xs in
            Poly $ map (/c) xs

    signum (Poly xs) = Poly [last xs]

    fromInteger int = Poly [fromInteger int]

leadingCoef :: Poly a -> a
leadingCoef (Poly xs) = last xs

degree :: Poly a -> Int
degree (Poly xs) = 
    if length xs == 0
        then error "degree of the zero polynomial"
        else length xs - 1

pQuotRem :: (Fractional a) => Poly a -> Poly a -> (Poly a, Poly a)
pQuotRem x y
    | x == 0              = (0, 0)
    | y == 0              = error "division by zero"
    | degree x < degree y = (0, x) 
    | otherwise           = 
        let fac = Poly [leadingCoef x / leadingCoef y]
                * Poly (replicate (degree x - degree y) 0 ++ [1])
            (q,r) = pQuotRem (x - y * fac) y in
        (fac + q, r)

pDiv :: (Fractional a) => Poly a -> Poly a -> Poly a
pDiv x y = fst (pQuotRem x y)

pMod :: (Fractional a) => Poly a -> Poly a -> Poly a
pMod x y = snd (pQuotRem x y)
