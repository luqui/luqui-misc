import Data.List
import System
import qualified Data.Sequence as Seq
import System.Random
import qualified Data.Foldable as Foldable

qsort1 :: (Ord a) => [a] -> [a]
qsort1 [] = []
qsort1 (x:xs) = qsort1 less ++ [x] ++ qsort1 greater
    where
    (less,greater) = partition (<= x) xs

qsort2 :: (Ord a) => [a] -> [a]
qsort2 xs = go xs []
    where
    go [] = id
    go (x:xs) = go less . (x:) . go greater
        where
        (less,greater) = partition (<= x) xs

qsort3 :: (Ord a) => [a] -> [a]
qsort3 = Foldable.toList . go . Seq.fromList
    where
    go l = case Seq.viewl l of
        Seq.EmptyL  -> Seq.empty
        x Seq.:< xs -> let (less,greater) = seqPartition (<= x) xs
                       in less Seq.>< Seq.singleton x Seq.>< greater
                
seqPartition :: (a -> Bool) -> Seq.Seq a -> (Seq.Seq a, Seq.Seq a)
seqPartition p l = case Seq.viewl l of
    Seq.EmptyL  -> (Seq.empty, Seq.empty)
    x Seq.:< xs -> let ~(t,f) = seqPartition p xs in
                     if p x
                        then (x Seq.<| t, f)
                        else (t, x Seq.<| f)

main = do
    [num, typ] <- getArgs
    let fun = case typ of
         "1" -> qsort1
         "2" -> qsort2
         "3" -> qsort3
    let list = take (read num) (randoms (mkStdGen 42))
    let r = fun list
    length r `seq` print (head r :: Int)
