import Data.Array
import Control.Monad.State
import Data.Maybe
import Data.List
import System.IO
import Data.Function (on)

type Move  = (XO, Int)

data XO = X | O
    deriving Eq

instance Show XO where
    show X = "X"
    show O = "O"

other :: XO -> XO
other X = O
other O = X

data Board = Board (Array Int (Maybe XO))

instance Show Board where
    show (Board b) = "+---+---+---+\n"
                  ++ "| " ++ p 1 ++ " | " ++ p 2 ++ " | " ++ p 3 ++ " |\n"
                  ++ "+---+---+---+\n"
                  ++ "| " ++ p 4 ++ " | " ++ p 5 ++ " | " ++ p 6 ++ " |\n"
                  ++ "+---+---+---+\n"
                  ++ "| " ++ p 7 ++ " | " ++ p 8 ++ " | " ++ p 9 ++ " |\n"
                  ++ "+---+---+---+\n"
        where
            p :: Int -> String
            p ix = maybe " " show (b!ix)

emptyBoard = Board (array (1,9) $ zip [1..9] (repeat Nothing))

winTest :: Board -> (Int, Int, Int) -> Maybe XO
winTest (Board board) (ia, ib, ic) = markWinTest (board ! ia) (board ! ib) (board ! ic)

markWinTest :: Maybe XO -> Maybe XO -> Maybe XO -> Maybe XO
markWinTest (Just a) (Just b) (Just c)
    | a == b && b == c
        = Just a
markWinTest _ _ _ = Nothing

win :: Board -> Maybe XO
win board = foldr mplus Nothing $
                map (winTest board) [(1,2,3),
                                     (4,5,6),
                                     (7,8,9),
                                     (1,4,7),
                                     (2,5,8),
                                     (3,6,9),
                                     (1,5,9),
                                     (3,5,7)]

full :: Board -> Bool
full (Board board) = all isJust (elems board)

move :: Move -> Board -> Maybe Board
move (pl, s) (Board board)
    | s `elem` [1..9] = maybe (Just $ Board $ board // [(s, Just pl)])
                              (const Nothing)
                              (board ! s)
    | otherwise       = Nothing


wins :: XO -> Board -> Bool
wins pl = maybe False (== pl) . win

allBoards :: XO -> Board -> [Board]
allBoards pl board = 
    concatMap maybeToList
        (map (\s -> move (pl, s) board) [1..9])

data Player = AI
            | Human String

act :: Player -> XO -> Board -> IO (Maybe Board)
act player@(Human name) pl board = do
    putStr $ "Your move, " ++ name ++ " (" ++ show pl ++ "): "
    space <- readLn
    maybe (do putStrLn "Invalid move"
              act player pl board)
          (return . Just)
          (move (pl,space) board)

--   The AI follows   --

act AI pl board = return $ aiMakeMove pl board

data Rating = MayLose | WontLose | WillWin
    deriving (Eq, Ord, Enum)

finiteMin :: (Eq a) => (a -> a -> Bool) -> a -> a -> [a] -> a
finiteMin _ _ mx [] = mx
finiteMin less mn mx (a:as) 
    | a == mn   = mn
    | otherwise = let mas = finiteMin less mn mx as in
                      if mas `less` a
                          then mas
                          else a

ratingMin :: [Rating] -> Rating
ratingMin = finiteMin (<) MayLose WillWin

ratingMax :: [Rating] -> Rating
ratingMax = finiteMin (>) WillWin MayLose
                          

aiMove :: XO -> Board -> Rating
aiMove pl board =
    makeRating pl board $ ratingMin $ do
            oppmove <- allBoards (other pl) board
            return $ makeRating pl oppmove $ ratingMax $ do
                mymove <- allBoards pl oppmove
                return $ aiMove pl mymove

makeRating :: XO -> Board -> Rating -> Rating
makeRating pl board def 
    | wins pl board         = WillWin
    | wins (other pl) board = MayLose
    | full board            = WontLose
    | otherwise             = def

maxRating :: (Board -> Rating) -> [Board] -> Board
maxRating f = maximumBy (compare `on` f)

aiMakeMove :: XO -> Board -> Maybe Board
aiMakeMove pl board = 
    let boards = allBoards pl board in
    if null boards
        then Nothing
        else Just $ maxRating (aiMove pl) boards 

--    End of AI   --


playGame :: (Player,Player) -> StateT (XO,Board) IO (Maybe XO)
playGame (cur,oth) = do
    (pl, board) <- get
    liftIO $ print board
    maybe (if full board
                then return Nothing
                else (do mnextboard <- liftIO $ act cur pl board
                         maybe (return $ Just $ other pl)
                               (\newboard -> do put (other pl, newboard)
                                                playGame (oth,cur))
                               mnextboard))
          (return . Just)
          (win board)


makePlayer :: String -> Player
makePlayer "AI" = AI
makePlayer name = Human name

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    putStr "Player 1: "
    p1 <- getLine
    putStr "Player 2: "
    p2 <- getLine
    (mwinner,(_,finalboard)) <- runStateT (playGame (makePlayer p1, makePlayer p2)) (X,emptyBoard)
    putStrLn $ maybe "No winner" (\winner -> show winner ++ " wins!") mwinner
    print finalboard
