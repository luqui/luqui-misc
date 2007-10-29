import Data.Maybe
import System.IO
import Control.Monad

-- The Omega monad.
-- It's like the list monad, but all results produced are reachable
-- in a finite number of steps.  I.e. the list it returns is of order
-- type omega or less.

-- Define an omega-list to be a list of order type omega or less.

assert :: (Monad m) => Bool -> m ()
assert c = if c then return () else fail "assertion failed"

-- Given a omega-list of omega-lists, return an omega-list ordering
-- the members of members of the argument.
diagonal :: [[a]] -> [a]
diagonal = diagonal' 0
	where
	-- We need diagonal' to ensure that the function terminates
	-- when given a finite matrix.
	diagonal' _ [] = []
	diagonal' n xss = 
		let (str,xss') = stripe n xss in
		str ++ diagonal' (n+1) xss'
	
	stripe 0 xss = ([],xss)
	stripe n []  = ([],[])
	stripe n ([]:xss) = stripe n xss
	stripe n ((x:xs):xss) = 
		let (nstripe, nlists) = stripe (n-1) xss in
		(x:nstripe, xs:nlists)

newtype Omega a = Omega { runOmega :: [Maybe a] }
	deriving Show

instance Monad Omega where
	Omega m >>= f  =  Omega $ diagonal $ map (runOmega . maybe (fail "") f) m
	return x       =  Omega [Just x]
	fail _         =  Omega [Nothing]

from :: [a] -> Omega a
from [] = Omega [Nothing]
from xs = Omega $ map Just xs

-- For example, this function will generate a list of pairs in N^2,
-- with the property that every pair in N^2 is in a "finiteth" position
-- in the list.
sums :: Omega (Int,Int)
sums = do
	x <- from [0..]
	y <- from [0..]
	assert (x == 3)
	return (x,y)

main :: IO ()
main = do
	hSetBuffering stdout NoBuffering
	print $ takeWhile ((< 2000) . snd) $ catMaybes $ runOmega sums
