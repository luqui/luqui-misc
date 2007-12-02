import qualified Data.Array.Diff as Array
import Data.Maybe
import Data.List
import Control.Monad
import Data.Char
import System.IO

type Board = Array.DiffArray (Int,Int) (Maybe Int)

findNext :: Board -> Maybe (Int,Int)
findNext bd = maybeHead $ do
    x <- [1..9]
    y <- [1..9]
    if isNothing $ bd Array.! (x,y)
       then return (x,y)
       else []

    where
    maybeHead (x:xs) = Just x
    maybeHead [] = Nothing

fillInNext :: Board -> [Maybe ((Int,Int),Board)]
fillInNext bd = do
    case findNext bd of
         Just p' -> do
            r <- [1..9]
            return $ Just (p', bd Array.// [(p', Just r)])
         Nothing -> return Nothing

slices :: (Int,Int) -> Board -> [[Maybe Int]]
slices (x,y) bd = 
    [ slice [ (x',y) | x' <- [1..9] ]
    , slice [ (x,y') | y' <- [1..9] ]
    , slice [ (x',y') | x' <- [fl x..fl x+2], y' <- [fl y..fl y+2] ]
    ]
    where
    slice = map (bd Array.!)
    fl n = (3 * ((n - 1) `div` 3)) + 1

satisfy :: [Maybe Int] -> Bool
satisfy xs = nub filled == filled
    where
    filled = catMaybes xs

checkBoard :: (Int,Int) -> Board -> Bool
checkBoard ix bd = all satisfy (slices ix bd)

solve :: Board -> [Board]
solve bd = do
    b <- fillInNext bd
    case b of
         Just (ix,b') 
            | checkBoard ix b' -> solve b'
            | otherwise        -> []
         Nothing -> return bd



main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    init <- fmap concat $ forM [1..9] $ \lineno -> do
        line <- fmap (map readDig) getLine
        return $ zip [(x,lineno) | x <- [1..9]] line
    let bd = Array.array ((1,1),(9,9)) init
    showSolution (solve bd)
    where
    readDig '.' = Nothing
    readDig x | isDigit x = Just (ord x - ord '0')
              | otherwise = error "Bad Input"

    showSolution [] = do
        putStrLn "--"
        putStrLn "No more solutions"
    showSolution (s:ss) = do
        putStrLn "--"
        showBoard s
        putStr "Show another (y/n)? "
        ch <- getLine
        case ch of
            "y" -> showSolution ss
            _   -> return ()

    showDig Nothing = '.'
    showDig (Just x) = chr (x + ord '0')

    showBoard bd = do
        forM_ [1..9] $ \lineno -> do
            forM_ [1..9] $ \colno -> do
                putChar $ showDig (bd Array.! (colno,lineno))
            putChar '\n'
