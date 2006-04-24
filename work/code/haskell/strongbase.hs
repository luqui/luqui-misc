
baseup :: Integer -> Integer -> Integer -> Integer -> Integer
baseup base base' pow 0 = 0
baseup base base' pow n = base' ^ (baseup base base' 0 pow) 
				        * (coef + baseup base base' (pow+1) ((n - coef) `div` base))
	where
	coef = n `mod` base

baseseq :: Integer -> Integer -> [Integer]
baseseq base 0 = [0]
baseseq base n = n : baseseq (base+1) (baseup base (base+1) 0 n - 1)
