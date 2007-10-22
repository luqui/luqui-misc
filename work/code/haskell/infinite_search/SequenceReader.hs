module SequenceReader 
    ( )
where

import Control.Monad.RWS
import Data.Maybe
import Debug.Trace

newtype SequenceReader a = SR { unSR :: RWS [Bool] () Int a }

instance Monad SequenceReader where
    return = SR . return
    SR a >>= f = SR (a >>= unSR . f)

readIdx :: Int -> SequenceReader Bool
readIdx z = SR $ do
    bs <- ask
    modify (max z)
    return (bs !! z)

runSR :: SequenceReader a -> [Bool] -> (a,Int)
runSR (SR seq) bs = 
    let (a,s,()) = runRWS seq bs 0 in (a,s)

allSeqs :: Int -> [[Bool]]
allSeqs n =
    case n `compare` 0 of
        LT -> []
        EQ -> [[]]
        GT -> do
            t <- allSeqs (n-1)
            h <- [False,True]
            return (h:t)

search :: SequenceReader Bool -> Maybe [Bool]
search rdr = search' []
    where
    search' xs =
        trace ("searching " ++ show xs) $ 
        case runSR rdr (xs ++ [False,False ..]) of
            (True, _)  -> Just (xs ++ [False,False ..])
            (False, d) ->
                msum (map (\r -> search' (xs ++ r)) $ tail $ allSeqs (d + 1 - length xs))

elem16 :: SequenceReader Bool
elem16 = do
    return False
