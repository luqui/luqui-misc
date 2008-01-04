import ASM
import Control.Applicative
import Debug.Trace
import Control.Monad

main = do
    (state, state') <- initAction $ do
        state <- newSV 0
        state' <- integral state
        return (state, state')

    let stepCond = do
            s <- getVar state
            return (s < 7)
        stepAction = do
            s <- getVar state
            g <- getGeneration 
            cliftIO $ putStrLn $ "(" ++ show g ++ ") Incrementing s from " 
                                 ++ show s ++ " to " ++ show (s+1)
            when (floor s `mod` 3 == 0) $ do
                s' <- getVar state'
                cliftIO $ putStrLn $ "  state' is " ++ show s'
            writeVar state (s+1)
        stepRule = Rule "step" stepCond stepAction

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
