module Functionator.CrappyConsoleUI where

import System.IO
import Data.Supply
import qualified Data.Map as Map
import Functionator.AST
import Functionator.Pointer
import Functionator.MockFunctions
import Control.Monad

consoleUI :: IO ()
consoleUI = do
        hSetBuffering stdout NoBuffering
        supply <- newSupply 0 succ
        ui supply (newPointer mockEnv (makeArrow (TVar "Int") (TVar "Int")))
    where
    ui s ptr = do
        print ptr
        putStr "> "
        cmd <- getLine
        runCmd cmd s ptr
    runCmd "l"  s ptr = ui s (goAppL ptr)
    runCmd "r"  s ptr = ui s (goAppR ptr)
    runCmd "d"  s ptr = ui s (goLambda ptr)
    runCmd "ma" s ptr = ui (supplyRight s) (makeApp (supplyLeft s) ptr)
    runCmd ('m':'l':' ':var) s ptr =
        ui (supplyRight s) (makeLambda (supplyLeft s) var ptr)
    runCmd ('m':'v':' ':var) s ptr =
        ui (supplyRight s) (makeVar (supplyLeft s) var ptr)
    runCmd "locals" s ptr = do
        forM_ (Map.toList $ cxtEnv (pCxt ptr)) $ \(k,v) -> do
            putStr $ k ++ " :: " ++ show v
        ui s ptr
    runCmd "globals" s ptr = do
        forM_ (Map.toList $ pEnv ptr) $ \(k,v) -> do
            putStr $ k ++ " :: " ++ show v
        ui s ptr
