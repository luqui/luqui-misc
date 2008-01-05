import ASM
import Control.Applicative
import Debug.Trace
import Control.Monad

main = do
    state <- initAction $ newSV 0

    let stepCond = do
            s <- getVar state
            return (s < 7)
        stepAction = do
            s <- getVar state
            naughtyLiftIO $ putStrLn $ "Incrementing s from " 
                                    ++ show s ++ " to " ++ show (s+1)
            writeVar state (s+1)
        stepRule = stepCond ==> stepAction

    cxt <- newASMContext [stepRule]
    putStrLn "1"
    cxt <- stepASM cxt
    putStrLn "2"
    cxt <- stepASM cxt
    putStrLn "3"
    cxt <- stepASM cxt
    putStrLn "4"
    cxt <- stepASM cxt
    putStrLn "5"
    cxt <- stepASM cxt
    putStrLn "6"
    cxt <- stepASM cxt
    putStrLn "7"
    cxt <- stepASM cxt
    putStrLn "8"
    cxt <- stepASM cxt
    putStrLn "9"
    cxt <- stepASM cxt
    putStrLn "10"
    cxt <- stepASM cxt

    return ()
