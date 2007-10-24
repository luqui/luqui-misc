{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- Turing machine simulator.

import qualified Data.Map as Map
import Control.Monad.State
import Control.Concurrent

type Sym = Int
type MState = Char

data Motion
    = MoveLeft | MoveRight

data Rule
    = Rule { ruleState :: MState
           , ruleMove  :: Motion
           , ruleSym   :: Sym
           }

type Machine = Map.Map (MState,Sym) Rule

data Tape
    = Tape { tapeLeft  :: [Sym]
           , tapeHere  :: Sym
           , tapeRight :: [Sym]
           }

showTape :: Bool -> Tape -> IO ()
showTape showHead (Tape ls h rs) = do
    let left  = concatMap show $ reverse ls
        here  = show h
        right = concatMap show rs
    let sp = map (const ' ')
    putStrLn $ left ++ here ++ right
    when showHead $ 
        putStrLn $ sp left ++ "^" ++ sp (tail here) ++ sp right

writeTape :: Sym -> Tape -> Tape
writeTape s t = t { tapeHere = s }

moveTape :: Motion -> Tape -> Tape
moveTape MoveLeft  (Tape []     h rs)     = Tape []     0 (h:rs)
moveTape MoveLeft  (Tape (l:ls) h rs)     = Tape ls     l (h:rs)
moveTape MoveRight (Tape ls     h [])     = Tape (h:ls) 0 []
moveTape MoveRight (Tape ls     h (r:rs)) = Tape (h:ls) r rs

data World
    = World { worldMState :: MState
            , worldTape   :: Tape
            }

stepMachine :: (MonadState World m) => Machine -> m ()
stepMachine machine = do
    World mstate tape <- get
    Rule { ruleSym = sym, ruleMove = move, ruleState = state } 
        <- Map.lookup (mstate, tapeHere tape) machine
    put $ World state (moveTape move . writeTape sym $ tape)

traceMachine :: (MonadState World m, MonadIO m) => Machine -> m ()
traceMachine machine = do
    stepMachine machine
    World mstate tape <- get
    liftIO $ showTape True tape
    liftIO $ threadDelay 100000
    when (mstate /= 'H') $ traceMachine machine

runMachine :: (MonadState World m, MonadIO m) => Machine -> m ()
runMachine machine = run' 0
    where 
    run' !n = do
        stepMachine machine
        World mstate tape <- get
        if mstate == 'H'
            then status n tape
            else run' (n+1)
    status n tape = liftIO $ do
        putStrLn $ show n ++ " steps"
        showTape False tape


complexCounter :: Machine
complexCounter = Map.fromList [ (('a',0), Rule 'b' MoveLeft  1)
                              , (('a',1), Rule 'a' MoveRight 1)
                              , (('b',0), Rule 'a' MoveRight 0)
                              , (('b',1), Rule 'c' MoveLeft  0)
                              , (('c',0), Rule 'c' MoveRight 0)
                              , (('c',1), Rule 'd' MoveLeft  1)
                              , (('d',0), Rule 'e' MoveLeft  1)
                              , (('d',1), Rule 'a' MoveRight 0)
                              , (('e',0), Rule 'b' MoveLeft  0)
                              , (('e',1), Rule 'H' MoveLeft  1)
                              ]

chaotic :: Machine
chaotic = Map.fromList [ (('a',0), Rule 'b' MoveLeft  1)
                       , (('a',1), Rule 'b' MoveRight 1)
                       , (('b',0), Rule 'c' MoveRight 1)
                       , (('b',1), Rule 'e' MoveLeft  0)
                       , (('c',0), Rule 'd' MoveRight 0)
                       , (('c',1), Rule 'a' MoveLeft  0)
                       , (('d',0), Rule 'a' MoveLeft  1)
                       , (('d',1), Rule 'd' MoveRight 0)
                       , (('e',0), Rule 'H' MoveLeft  1)
                       , (('e',1), Rule 'c' MoveLeft  0)
                       ]

bb5 :: Machine
bb5 = Map.fromList [ (('a',0), Rule 'b' MoveLeft  1)
                   , (('a',1), Rule 'a' MoveLeft  1)
                   , (('b',0), Rule 'c' MoveRight 1)
                   , (('b',1), Rule 'b' MoveRight 1)
                   , (('c',0), Rule 'a' MoveLeft  1)
                   , (('c',1), Rule 'd' MoveRight 1)
                   , (('d',0), Rule 'a' MoveLeft  1)
                   , (('d',1), Rule 'e' MoveRight 1)
                   , (('e',0), Rule 'H' MoveLeft  1)
                   , (('e',1), Rule 'c' MoveRight 0)
                   ]


main :: IO ()
main = do
    evalStateT (runMachine bb5) (World 'a' (Tape [] 0 [])) 
