{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}

module Typist.Run (
    runAST, runCode,
) where

import Typist.AST
import Typist.Eval
import Typist.Prim
import Typist.Syntax
import Control.Monad.Reader

runAST :: AST -> Val
runAST = evalWithPad nativePad

runCode :: String -> Val
runCode = runAST . parseAST
