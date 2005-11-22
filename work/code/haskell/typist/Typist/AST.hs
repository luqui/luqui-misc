module Typist.AST (
    VarName,
    AST(..),
    ASTLit(..),
) where

type VarName = String

data AST
    = Lambda { lamParam :: VarName, lamBody :: AST }
    | App    { appFun :: AST, appArg :: AST }
    | Var    { varName :: VarName }
    | Lit    { litLit :: ASTLit }
    deriving Show

data ASTLit 
    = Int    { intVal :: Integer }
    | Bool   { boolVal :: Bool }
    deriving Show


