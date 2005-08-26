import System.Random
import Data.Map as Map
import Data.Complex

type Amplitude = Complex Float

data EqX a = EqX a

eqx :: EqX a -> a
eqx (EqX x) = x

data Ord a => Superposition a = 
    Superposition (Map (EqX a) Amplitude)

superpose :: Ord a => [(a, Amplitude)] -> Superposition a
superpose xs = Superposition (Map.fromListWith (+) xs)

scale :: Ord a => Amplitude -> Superposition a -> Superposition a
scale a (Superposition s) = Superposition $ Map.map (a *) s

states :: Ord a => Superposition a -> [(a, Amplitude)]
states (Superposition ampl) = Map.toList ampl

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

instance Monad Superposition where
    (>>=) j f = superpose $ concatMap (\ (k, v) -> states $ scale v (f k)) (states j)
    return x  = superpose [(x, 1)]

mully :: Superposition Int
mully = do
    c <- superpose [(0, 1), (1, 0 :+ 1)]
    d <- superpose [(0, 1), (1, 1)]
    return $ c * d
    

main = print =<< (select $ superpose $ 
    [("hi",  1   :+ 0), 
     ("lo",  1   :+ 0),
     ("lo", (-1) :+ 0)])
