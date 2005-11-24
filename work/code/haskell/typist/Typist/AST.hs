module Typist.AST (
    VarName,
    AST(..),
    ASTLit(..),
    primitives,
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

primitives :: [VarName]
primitives = words "plus neg times leq if True False fix"
