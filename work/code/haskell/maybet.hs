{-#OPTIONS -fglasgow-exts #-}

import System.IO
import Control.Monad.Trans

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance (Monad m) => Monad (MaybeT m) where
    (MaybeT mon) >>= f   = 
        MaybeT (mon >>= maybe (return Nothing) (runMaybeT . f))
    return               = MaybeT . return . Just

instance MonadTrans MaybeT where
    lift mon = MaybeT (mon >>= return . Just)



guesser :: String -> MaybeT IO ()
guesser word = do
    lift $ putStr "Guess the word I'm thinking of: "
    guess <- lift $ getLine
    if guess == word
        then return ()
        else MaybeT (return Nothing)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    runMaybeT (guesser "foo" >> guesser "bar" >> guesser "baz") >> return ()
