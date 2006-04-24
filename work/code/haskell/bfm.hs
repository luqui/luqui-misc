-- The Omega monad.
-- It's like the list monad, but all results produced are reachable
-- in a finite number of steps.  I.e. the list it returns is of order
-- type omega or less.

-- Define an omega-list to be a list of order type omega or less.

-- Given a omega-list of omega-lists, return an omega-list ordering
-- the members of members of the argument.
diagonal :: [[a]] -> [a]
diagonal = diagonal' 0
	where
	-- We need diagonal' to ensure that the function terminates
	-- when given a finite matrix.
	diagonal' n xss = 
		let (str,xss') = stripe n xss in
		str ++ if null xss' 
				then []
				else diagonal' (n+1) xss'
	
	stripe 0 xss = ([],xss)
	stripe n []  = ([],[])
	stripe n ([]:xss) = stripe n xss
	stripe n ((x:xs):xss) = 
		let (nstripe, nlists) = stripe (n-1) xss in
		(x:nstripe, xs:nlists)

newtype Omega a = Omega { runOmega :: [a] }
	deriving Show

instance Monad Omega where
	Omega m >>= f  =  Omega $ diagonal $ map (runOmega . f) m
	return x       =  Omega [x]
	fail _         =  Omega []

-- For example, this function will generate a list of pairs in N^2,
-- with the property that every pair in N^2 is in a "finiteth" position
-- in the list.
sums :: Omega (Int,Int)
sums = do
	x <- Omega [0..]
	y <- Omega [0..]
	return (x,y)
