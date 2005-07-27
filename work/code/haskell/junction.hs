import System.Random
import Data.Map as Map
import Data.Complex

type Amplitude = Complex Float

data Ord a => Superposition a = 
    Superposition (Map a Amplitude)

superpose :: Ord a => [(a, Amplitude)] -> Superposition a
superpose xs = Superposition (Map.fromListWith (+) xs)

_select :: Ord a => Int -> a -> [(a, Amplitude)] -> IO a
_select _ cur [] = return cur
_select num cur ((val, prob):rest) = do
    sel <- randomRIO (0,1)
    if sel <= magnitude prob / realToFrac num
        then _select (num+1) val rest
        else _select (num+1) cur rest

select :: Ord a => Superposition a -> IO a
select (Superposition set) =
    let ((val, _):rest) = Map.assocs set
        in _select 2 val rest

main = print =<< (select $ superpose $ 
    [("hi",  1   :+ 0), 
     ("lo",  1   :+ 0),
     ("lo", (-1) :+ 0)])
