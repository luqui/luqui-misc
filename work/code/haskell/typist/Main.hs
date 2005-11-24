module Main where

import Typist.Run
import System.Environment

main :: IO ()
main = do
    [file] <- getArgs
    code <- readFile file
    print $ runCode code
