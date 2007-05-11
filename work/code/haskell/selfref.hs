-- Fight with ambiguity!

-- Fill in the blanks of the following with the correct numbers:
-- The number of occurrences of 0 is _; 1 is _; 2 is _; 3 is _; 4 is _

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type OcMap = Map.Map Int Int
type Range = [Int]

countOccurrences :: OcMap -> OcMap
countOccurrences = 
    Map.foldWithKey 
        (\k v -> insertOn k . insertOn v)
        Map.empty
    where
    -- separate into digits
    insertOn :: Int -> OcMap -> OcMap
    insertOn = foldr (\x -> (Map.insertWith (+) (read [x]) 1 .)) id . show

prune :: Range -> OcMap -> OcMap
prune r m = Map.intersection m $ Map.fromList [ (n,undefined) | n <- r ]

fixPoint :: (Eq a) => (a -> a) -> a -> a
fixPoint f a = 
    let next = f a in
        if next == a 
            then a 
            else fixPoint f next

fixPointMax :: (Eq a) => Int -> (a -> a) -> a -> Maybe a
fixPointMax 0 _ _ = Nothing
fixPointMax n f a =
    let next = f a in
        if next == a
            then Just a
            else fixPointMax (n-1) f next

solve :: Range -> OcMap
solve r = fixPoint (prune r . countOccurrences) $ Map.fromList [ (n,0) | n <- r ]

solveMax :: Int -> Range -> Maybe OcMap
solveMax n r = fixPointMax n (prune r . countOccurrences) $ Map.fromList [ (n,0) | n <- r ]
