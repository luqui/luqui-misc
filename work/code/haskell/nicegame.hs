{-# OPTIONS_GHC -fglasgow-exts -fth #-}

import Accessor
import Control.Monad.State

data GameState
    = GameState { _p1bid :: Int
                , _p2bid :: Int
                , _score :: Int 
                }

type Game a = StateT GameState IO a

p1bid = $(accessor '_p1bid)
p2bid = $(accessor '_p2bid)
score = $(accessor '_score)

(=:) :: (MonadState s m) => Accessor s a -> a -> m ()
a =: x  = writeVal a x

(+=) :: (Num a, MonadState s m) => Accessor s a -> a -> m ()
a += x  = do
    a_ <- readVal a
    a =: (a_ + x)

(-=) :: (Num a, MonadState s m) => Accessor s a -> a -> m ()
a -= x  = do
    a += (-x)

loop :: (Monad m) => m a -> m b
loop m = m >> loop m

main :: IO ()
main = flip evalStateT (GameState 0 0 0) $ loop $ do
    score_ <- readVal score
    liftIO $ putStrLn $ "Score is " ++ show score_
    liftIO $ putStr $ "Player 1, bid: "
    (p1bid =:) =<< liftIO readLn
    liftIO $ putStr $ "Player 2, bid: "
    (p2bid =:) =<< liftIO readLn
    cmp <- liftM2 compare (readVal p1bid) (readVal p2bid)
    case cmp of
        LT -> do
            liftIO $ putStrLn "Player 2 scores!"
            score -= 1
        EQ -> do
            liftIO $ putStrLn "Nobody scores!"
        GT -> do
            liftIO $ putStrLn "Player 1 scores!"
            score += 1
