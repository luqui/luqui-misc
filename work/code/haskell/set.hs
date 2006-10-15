import Data.List
import System.Random

type Card = [Int]

isHetero :: [Int] -> Bool
isHetero xs = nub xs == xs

isHomo :: [Int] -> Bool
isHomo xs = length (nub xs) == 1

isSet :: [Card] -> Bool
isSet cards = all (\x -> isHetero x || isHomo x) $ transpose cards

combs :: Int -> [a] -> [[a]]
combs 0 xs = [[]]
combs n xs = do
	m <- [0 .. length xs - n]
	let (x:xs') = drop m xs
	rest <- combs (n-1) xs'
	return (x:rest)

hasSet :: Int -> [Card] -> Bool
hasSet n cards = any isSet $ combs n cards

genCard :: [Int] -> IO Card
genCard rng = mapM (\r -> randomRIO (0,r-1)) rng

genDeck :: Int -> [Int] -> IO [Card]
genDeck n rng = mapM (const $ genCard rng) [0..n-1]

countSetDecks :: Int -> Int -> Int -> [Int] -> IO Int
countSetDecks ndecks set sz rng = do
	decks <- mapM (const $ genDeck sz rng) [0..ndecks-1]
	return $ length $ filter (hasSet set) decks

main :: IO ()
main = do
	mapM_ printDeckLine [1..]  -- apparently 21 is the "set ramsey number"
	where
	printDeckLine :: Int -> IO ()
	printDeckLine sz = do
		sets <- countSetDecks 10000 3 sz [3,3,3,3]
		putStrLn $ show sz ++ "\t" ++ show sets
