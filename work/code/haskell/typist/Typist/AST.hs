module Typist.AST (
    VarName,
    AST(..),
) where

type VarName = String

data AST
    = Lambda { lamParam :: VarName, lamBody :: AST }
    | App    { appFun :: AST, appArg :: AST }
    | Var    { varName :: VarName }
