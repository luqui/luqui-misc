import Data.Array

type Move  = (XO, Int)

data XO = X | O
    deriving Eq

data Board = Board (Array Int (Maybe XO))

emptyBoard = Board (array (1,9) $ zip [1..9] (repeat Nothing))

winTest :: Board -> (Int, Int, Int) -> Maybe XO
winTest (Board board) (ia,ib,ic) = markWinTest (board ! ia) (board ! ib) (board ! ic)

markWinTest :: Maybe XO -> Maybe XO -> Maybe XO -> Maybe XO
markWinTest (Just a) (Just b) (Just c)
    | a == b && b == c
        = Just a
markWinTest _ _ _ = Nothing

win :: Board -> Maybe XO
win board = foldr mplus Nothing 
                [(1,2,3),
                 (4,5,6),
                 (7,8,9),
                 (1,4,7),
                 (2,5,8),
                 (3,6,9),
                 (1,5,9),
                 (3,5,7)]

move :: Board -> Move -> Maybe Board
move board (pl, s) = maybe (board // [(s, Just pl)])
                           (const Nothing)
