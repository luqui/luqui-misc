import Data.Ratio

nextseq :: (Num a) => [a] -> a
nextseq rs = 
    let x = last rs in
        sum $ zipWith (\a b -> a * x^b) rs [0..]

genseq :: (Num a) => a -> [a]
genseq r = genseq'
    where
    genseq' = map head $ iterate (\as -> nextseq as : as) [r]
