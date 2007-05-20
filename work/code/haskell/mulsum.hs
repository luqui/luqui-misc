import Data.Maybe

nonUnitSums :: Integer -> [[Integer]]
nonUnitSums n = [n] : do
    sub <- [1..n-1]
    rest <- nonUnitSums sub
    return $ (n-sub):rest

isDescending :: (Ord a) => [a] -> Bool
isDescending []       = True
isDescending [_]      = True
isDescending (x:y:xs) = x >= y && isDescending (y:xs)

sums :: Integer -> [[Integer]]
sums = filter isDescending . nonUnitSums
