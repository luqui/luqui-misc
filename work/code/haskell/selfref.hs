-- Fight with ambiguity!

-- Fill in the blanks of the following with the correct numbers:
-- The number of occurrences of 0 is _; 1 is _; 2 is _; 3 is _; 4 is _

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type OcMap = Map.Map Int Int

countOccurrences :: OcMap -> OcMap
countOccurrences = 
    Map.foldWithKey 
        (\k v -> insertOn k . insertOn v)
        Map.empty
    where
    insertOn :: Int -> OcMap -> OcMap
    insertOn = foldr (\x -> (Map.insertWith (+) (read [x]) 1 .)) id . show

prune :: OcMap -> OcMap
prune m = Map.intersection m $ Map.fromList [ (n,undefined) | n <- [0..9] ]

fap :: Int -> (a -> a) -> (a -> a)
fap 0 _ = id
fap n f = f . fap (n-1) f

iter :: Int -> OcMap
iter n = fap n (prune . countOccurrences) $ Map.fromList [ (n,0) | n <- [0..9] ]
