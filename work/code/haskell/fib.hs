import qualified System
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import qualified Data.MemoCombinators as Memo

type FibState a = State.State (Map.Map Integer Integer) a

doFib :: Integer -> FibState Integer
doFib 0 = return 0
doFib 1 = return 1
doFib r = do
    cache <- State.get
    if r `Map.member` cache
        then Map.lookup r cache
        else do
            result <- if r `mod` 2 == 0
                        then do
                            let n = (r `div` 2) - 1
                            fibn <- doFib n
                            fibn1 <- doFib (n+1)
                            return $ fibn1^2 + 2 * fibn1 * fibn
                        else do
                            fibr1 <- doFib (r-1)
                            fibr2 <- doFib (r-2)
                            return $ fibr1 + fibr2
            State.modify $ Map.insert r result
            return result

fib :: Integer -> Integer
fib n = State.evalState (doFib n) Map.empty

fib' :: Integer -> Integer
fib' = Memo.integral go
    where
    go 0 = 0
    go 1 = 1
    go r = if r `mod` 2 == 0
            then let n = (r `div` 2) - 1
                     fibn = fib' n
                     fibn1 = fib' (n+1)
                 in fibn1^2 + 2 * fibn1 * fibn
            else fib' (r-1) + fib' (r-2)

main :: IO ()
main = do
    args <- System.getArgs
    case args of
        ("state":args) -> statemain args
        ("memo":args)  -> memomain args
        _ -> fail "Bad argument, expecting state or memo"
    where
    statemain args = do
        let nums = if null args then [0..] else map read args
        mapM_ print $ flip State.evalState Map.empty $ mapM doFib nums
    memomain args = do
        let nums = if null args then [0..] else map read args
        mapM_ (print . fib') nums
