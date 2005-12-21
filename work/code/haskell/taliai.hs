import Data.List
import Control.Monad.State
import System.IO

type Dice = Int
type Roll = [Int]

dice :: [Dice]
dice = [1..6]

nsPoints :: Dice -> Roll -> Int
nsPoints n = sum . filter (== n)

multis :: Int -> Roll -> [Dice]
multis n r = [ z | z <- dice, length (filter (== z) r) >= n ]

tripsPoints :: Roll -> Int
tripsPoints r = 
    if not . null $ multis 3 r
        then sum r
        else 0

quadsPoints :: Roll -> Int
quadsPoints r =
    if not . null $ multis 4 r
        then sum r
        else 0

fullHousePoints :: Roll -> Int
fullHousePoints r = 
    if not $ null fullHouse
        then 25
        else 0
    where
    fullHouse = do
        trips <- multis 3 r
        pair  <- multis 2 r
        if trips == pair
            then fail "that's just trips!"
            else return (trips,pair)

smallStraightPoints :: Roll -> Int
smallStraightPoints r = 
    if any (all (`elem` r)) straights
        then 30
        else 0
    where
    straights = [[1..4],[2..5],[3..6]]

largeStraightPoints :: Roll -> Int
largeStraightPoints r = 
    if any (all (`elem` r)) straights
        then 40
        else 0
    where
    straights = [[1..5],[2..6]]

yahtzeePoints :: Roll -> Int
yahtzeePoints r = 
    if not . null $ multis 5 r 
        then 50
        else 0

chancePoints :: Roll -> Int
chancePoints = sum

type Prizes = [(String, Roll -> Int)]

prizes :: Prizes
prizes = reverse $ 
         [ (show n ++ "s", nsPoints n) | n <- dice ]
      ++ [ ("trips",          tripsPoints), 
           ("quads",          quadsPoints), 
           ("full house",     fullHousePoints),
           ("small straight", smallStraightPoints),
           ("large straight", largeStraightPoints),
           ("yahtzee",        yahtzeePoints),
           ("chance",         chancePoints) ]

change :: Int -> a -> [a] -> [a]
change n new list = take n list ++ [new] ++ drop (n+1) list

rollDistro :: Roll -> [Int] -> [Roll]
rollDistro r [] = [r]
rollDistro r (n:ns) = do
    roll <- rollDistro r ns
    map (\to -> change n to roll) dice

posCombinations :: [[Int]]
posCombinations = combinations [0..4]
    where
    combinations (n:ns) = do
        rest <- combinations ns
        [rest, n:rest]
    combinations [] = [[]]

maxByEx :: (Ord o) => (a -> o) -> [a] -> a
maxByEx f = maximumBy (\a b -> f a `compare` f b)

maxScore :: Prizes -> Roll -> (String, Int)
maxScore prizs r = maxByEx snd rollPrizes
    where
    rollPrizes = [ (desc, f r) | (desc, f) <- prizs ]

(./) :: (Integral a, Integral b, Fractional c) => a -> b -> c
x ./ y = fromIntegral x / fromIntegral y

expectation :: Prizes -> [Roll] -> Double
expectation prizs rs = 
    sum (map (snd . maxScore prizs) rs) ./ length rs

bestRoll1 :: Prizes -> Roll -> ([Int], Double)
bestRoll1 prizs r = 
    let res = maxByEx expc posCombinations in (res, expc res)
    where
    expc = expectation prizs . rollDistro r 

getRoll :: String -> StateT Prizes IO Roll
getRoll msg = do
    liftIO $ putStr msg
    line <- liftIO getLine
    return $ map read $ words line

main' :: StateT Prizes IO ()
main' = do
    prizs <- get
    if null prizs
        then return ()
        else do
            roll  <- getRoll "What was your roll? "
            liftIO $ print $ bestRoll1 prizs roll
            reroll <- getRoll "What was your reroll? "
            liftIO $ print $ bestRoll1 prizs reroll
            rereroll <- getRoll "What was your final roll? "
            let (name,score) = maxScore prizs rereroll
            liftIO $ putStrLn $ "Choose '" ++ name ++ "' for " ++ show score ++ " points"
            put (filter (\x -> fst x /= name) prizs)
            main'

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    fmap fst $ runStateT main' prizes
