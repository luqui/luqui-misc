import Data.Ratio

main = print $ length set - 2   -- to get rid of 1/2 and 1/3
    where
    lb d = -((-d) `div` 3)
    ub d = (d `div` 2)
    set = [ n % d | d <- [1..10000::Int]
                  , n <- [lb d..ub d]
                  , gcd n d == 1
                  ]
