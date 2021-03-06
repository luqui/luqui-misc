import qualified Data.List as List
import qualified Control.Monad as Monad

data Decomp
    = One
    | Prime Decomp
    | Power Decomp Decomp
    | Mul [Decomp]

instance Show Decomp where
    show One = "1"
    show (Prime d) = "p_" ++ show d
    show (Power a b) = "(" ++ show a ++ "^" ++ show b ++ ")"
    show (Mul as)   = "(" ++ concat (List.intersperse " " (map show as)) ++ ")"

factor :: Integer -> [Integer]
factor n = factor' n 2
    where
    factor' n s 
        | n <= s    = [n]
        | otherwise = 
            if n `mod` s == 0
                then s:factor' (n `div` s) s
                else factor' n (s+1)

collect :: [Integer] -> [(Integer,Integer)]
collect [] = []
collect [x] = [(x,1)]
collect (x:xs) = 
    let (nh:rest) = collect xs in
        if fst nh == x
            then (x, snd nh + 1) : rest
            else (x,1) : nh : rest

isPrime :: Integer -> Bool
isPrime n = 
    case collect (factor n) of
        [(n,1)] -> True
        _       -> False

primes :: [Integer]
primes = filter isPrime [2..]

primeIndex :: Integer -> Integer
primeIndex n = foldr (\p i -> if p >= n then 1 else 1+i) 0 primes

decompose :: Integer -> Decomp
decompose 1 = One
decompose n = 
    case collect (factor n) of
        [(_,1)] -> Prime (decompose (primeIndex n))
        [(b,p)] -> Power (decompose b) (decompose p)
        xs      -> Mul $ map (\ (b,p) -> decompose (b^p)) xs

depth :: Decomp -> Integer
depth One = 0
depth (Prime x) = depth x + 1
depth (Power x y) = max (depth x) (depth y) + 1
depth (Mul xs) = maximum (map depth xs)

leaves :: Decomp -> Integer
leaves One = 1
leaves (Prime x) = leaves x
leaves (Power x y) = leaves x + leaves y
leaves (Mul xs) = sum (map leaves xs)

nodes :: Decomp -> Integer
nodes One = 1
nodes (Prime x) = 1 + nodes x
nodes (Power x y) = 1 + nodes x + nodes y
nodes (Mul xs) = 1 + sum (map nodes xs)

descendingSums :: Int -> Int -> [[Int]]
descendingSums 0 _ = [[]]
descendingSums n s = do
    first <- reverse [1..s]
    let remain = n-first
    rest <- descendingSums remain (min remain first)
    return (first:rest)
    

enumerate :: Int -> [Decomp]
enumerate 1 = [One]
enumerate n = (do n1 <- enumerate (n-1)
                  return $ Prime n1)
           ++ (do s <- [1..n-1]
                  n1 <- enumerate s
                  n2 <- enumerate (n-s)
                  return $ Power n1 n2)
           ++ (do ss <- descendingSums n n
                  Monad.when (length ss < 2) $ fail "avoid infinite loop"
                  return $ Mul (concatMap enumerate ss))

reconstruct :: Decomp -> Integer
reconstruct One = 1
reconstruct (Prime d) = primes !! fromInteger (reconstruct d - 1)
reconstruct (Power d e) = reconstruct d ^ reconstruct e
reconstruct (Mul xs) = product $ map reconstruct xs
