module Typist.Run (
    runAST,
) where

import Typist.AST
import Typist.Eval
import Typist.Prim
import Typist.Syntax
import Control.Monad.Reader

runAST :: AST -> Val
runAST ast = runReader (eval ast) nativePad

runCode :: String -> Val
runCode = runAST . parseAST
