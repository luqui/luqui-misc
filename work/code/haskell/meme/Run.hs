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

memeType :: String -> (Type,Type)
memeType prog = 
    let (ast,eqs) = typeAST builtinTypeEnv $ memeParse "." prog in
    boundType (reduceEquations eqs) (getType ast)
