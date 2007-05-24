import Data.Ratio

nextseq :: [Rational] -> Rational
nextseq rs = 
    let x = last rs in
        sum $ zipWith (\a b -> a * x^b) rs [0..]

genseq :: Rational -> [Rational]
genseq r = genseq'
    where
    genseq' = map head $ iterate (\as -> nextseq as : as) [r]
