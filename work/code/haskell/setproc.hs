import qualified Data.List as List
import qualified Data.Set  as Set

-- computes the set S such that:
--   init `subset` S
--   if x `elem` S then f x `subset` S
closure :: (Ord a) => (a -> [a]) -> [a] -> [a]
closure f init = closure' Set.empty init
    where
    closure' set [] = []
    closure' set (x:xs) = 
        let cur = List.nub $ filter (\t -> not (t `Set.member` set)) $ x:f x in
            cur ++ closure' (Set.union (Set.fromList cur) set) (xs ++ cur)
