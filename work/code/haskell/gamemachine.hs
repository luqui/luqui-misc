import Control.Comonad
import Control.Monad
import Data.Monoid
import Control.Arrow hiding (pure)
import Control.Applicative

newtype Future a = Future [(String,a)]
    deriving (Monoid)

instance Functor Future where
    fmap f (Future xs) = Future ((fmap.fmap) f xs)

data Game a = Game a (Future (Game a))

instance Functor Game where
    fmap f (Game x xs) = Game (f x) ((fmap.fmap) f xs)

instance Copointed Game where
    extract (Game x _) = x

-- Hey! Game is the cofree comonad over Future!
instance Comonad Game where
    duplicate g@(Game _ gs) = Game g (fmap duplicate gs)

finiteLabel :: a -> [(String, Game a)] -> Game a
finiteLabel g gs = Game g (Future gs)

finite :: Show a => a -> [Game a] -> Game a
finite g gs = finiteLabel g (zip (map (show.extract) gs) gs)

finiteGenerator :: Show a => (a -> [a]) -> a -> Game a
finiteGenerator gen g0 = finite g0 (map (finiteGenerator gen) (gen g0))


-- A sum game.  A move in x >+< y is a move in x or a move in y.
(>+<) :: Game a -> Game b -> Game (a,b)
(Game x xs) >+< (Game y ys) = Game (x,y) (xmoves `mappend` ymoves)
    where
    xmoves = (fmap.fmap) (\x' -> (x',y)) xs
    ymoves = (fmap.fmap) (\y' -> (x,y')) ys

-- A product game.  A move in x >*< y is a move in x and a move in y
(>*<) :: Game a -> Game b -> Game (a,b)
(Game x (Future xs)) >*< (Game y (Future ys)) = Game (x,y) (Future moves)
    where
    moves = [ (dx ++ " | " ++ dy, x >*< y) | (dx,x) <- xs, (dy,y) <- ys ]


runGame :: (a -> String) -> Game a -> IO ()
runGame showGame (Game x (Future xs)) = do
    putStrLn (showGame x)
    forM_ (zip [1..] xs) $ \(idx,(desc,_)) -> do
        putStrLn $ show idx ++ ". " ++ desc
    choice <- validate (\x -> 0 < x && x <= length xs) (putStr "? " >> readLn)
    putStrLn "--"
    runGame showGame . snd $ xs !! (choice-1)
    

validate :: (a -> Bool) -> IO a -> IO a
validate p io = do
    r <- io
    if p r then return r else validate p io
