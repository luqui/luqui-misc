module Run
    (
    )
where

import Type
import Parser
import Eval
import TypeInfer
import Prim

memeRun :: String -> IO Val
memeRun = memeRunProg "."

memeRunProg :: String -> String -> IO Val
memeRunProg name = runEval . eval . memeParse name

memeType :: String -> Type
memeType prog = 
    let (ast,eqs) = typeAST builtinTypeEnv $ memeParse "." prog in
    lowerBoundType (reduceEquations eqs) (getType ast)
