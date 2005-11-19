data Diff a
    = Add a
    | Del
    | Keep

apply :: [Diff a] -> [a] -> [a]
apply (Add a : as) xs     = a : apply as xs
apply (Del   : as) (x:xs) = apply as xs
apply (Keep  : as) (x:xs) = x : apply as xs
apply []           []     = []
