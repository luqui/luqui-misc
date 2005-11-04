import Control.Monad.Cont
import System.IO

hanoi :: (Show a, Num n) => n -> a -> a -> a -> (() -> ContT () IO ()) -> ContT () IO ()
hanoi 0 a b c escape = return ()
hanoi n a b c escape = do
    hanoi (n-1) a c b escape
    liftIO $ putStrLn ("move " ++ show a ++ " to " ++ show c)
    liftIO $ putStr "Continue? "
    continue <- liftIO getChar
    liftIO $ putStrLn []
    when (continue == 'n') $ escape ()
    hanoi (n-1) b a c escape

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    putStr "Number of rings? "
    nrings <- readLn
    runContT (callCC (hanoi nrings 'a' 'b' 'c')) return
    putStrLn "I hope you enjoyed playing.  Goodbye."
