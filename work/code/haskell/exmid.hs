{-# OPTIONS_GHC -fglasgow-exts #-}

import Control.Monad.Cont

exmid :: (MonadCont m) => m (Either (a -> m b) a)
exmid = exeither' exmid'
    where
    exmid' f g = either return g =<< callCC (\cc -> return . Left =<< f (cc . Right))
    exeither' e = e (return . Left) (return . Right)

type Prog a = forall r. ContT r IO a

mainProg :: Prog ()
mainProg = do
    name <- exmid 
    case name of
        Left f  -> do
            nm <- liftIO (putStr "Enter your name: " >> getLine) 
            answer <- f nm
            liftIO $ putStrLn $ "The meaning of life is " ++ answer
        Right nm -> liftIO $ putStrLn $ "Your name is " ++ nm


main :: IO ()
main = do
    runContT mainProg (const $ return ())
    return ()
