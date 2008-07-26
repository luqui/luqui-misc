-- writable n k = the number of ways to write n using numerals k or less
writable :: Int -> Int -> Integer
writable = \n k -> (cache !! n) !! k
    where
    cache = [ map (go n) [0..] | n <- [0..] ]
    go n 1 = 1
    go n k | k >= n = 1 + go n (n-1)
    go n k = sum [ writable (n-z) (min k z) | z <- [1..k] ]
