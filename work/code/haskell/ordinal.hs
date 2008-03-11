import Data.List

-- Ordinal [a0,a1,...] represents w^a0 + w^a1 + ...
-- With a0 >= a1 >= ...
newtype Ordinal = Ordinal [Ordinal] 
    deriving (Eq, Ord)


instance Show Ordinal where
    show (Ordinal [])                  = "0"
    show (Ordinal ones@(Ordinal []:_)) = show (length ones)
    show (Ordinal [x]) = "w^" ++ show x
    show (Ordinal xs) = "(" ++ concat (intersperse " + " [ "w^" ++ show x | x <- xs ]) ++ ")"

(@+) :: Ordinal -> Ordinal -> Ordinal
o @+ Ordinal [] = o
Ordinal xs @+ Ordinal (y:ys) = 
    Ordinal (takeWhile (>= y) xs ++ (y:ys))

(@*) :: Ordinal -> Ordinal -> Ordinal
Ordinal []     @* _ = Ordinal []
Ordinal (x:xs) @* Ordinal ys = 
    Ordinal (map (x @+) ys) @+ (Ordinal xs @* Ordinal ys)


-- Not sure how to do exponentiation
-- (@^) :: Ordinal -> Ordinal -> Ordinal


zero :: Ordinal
zero = Ordinal []

one :: Ordinal
one = Ordinal [zero]

w :: Ordinal
w = Ordinal [one]
