import Complex
import Random

type Amplitude = Complex Float

data Superposition a = 
    Superposition [(Amplitude, a)]

_select :: Int -> a -> [(Amplitude, a)] -> IO a
_select _ cur [] = return cur
_select num cur ((prob, val):rest) = do
    sel <- randomRIO (0,1)
    if sel <= magnitude prob / realToFrac num
        then _select (num+1) val rest
        else _select (num+1) cur rest

select :: Superposition a -> IO a
select (Superposition ((prob, val):rest)) =
    _select 2 val rest

main = print =<< (select $ Superposition [(1 :+ 0, "hi"), (0 :+ 1, "ack")])
