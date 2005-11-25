module Typist.AST (
    VarName,
    AST(..),
    ASTLit(..),
    primitives,
    GenType(..),
    SynT(..),
    TypeID,
) where

type VarName = String
type TypeID  = Integer

data AST
    = Lambda { lamParam :: VarName, lamBody :: AST }
    | ExpLambda { lamParam :: VarName, lamBody :: AST, lamTParam :: [TypeID], lamParamT :: SynT }
    | App    { appFun :: AST, appArg :: AST }
    | ExpApp { appFun :: AST, appArg :: AST, appTArg :: [SynT] }
    | Var    { varName :: VarName }
    | Lit    { litLit :: ASTLit }
    deriving Show

data ASTLit 
    = Int    { intVal :: Integer }
    | Bool   { boolVal :: Bool }
    deriving Show

data GenType typ
    = TFunc [TypeID] typ typ
    | TVar TypeID
    | TTop
    | TBot
    | TInt
    | TBool
    deriving Show

data SynT = SynT (GenType SynT)
    deriving Show

primitives :: [VarName]
primitives = words "plus neg times leq if True False fix"
