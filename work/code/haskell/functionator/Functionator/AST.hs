module Functionator.AST where

type Var = String

data Type
    = TVar  Var
    | TFree Int
    | TPi   Var Type
    | TApp  Type Type
    deriving Show

data Exp
    = EVar    Var
    | ELambda Var Type Exp
    | EApp    Exp Exp
    | EType   Type Exp
    | EHole
    deriving Show

data ExpZip
    = ZTop
    | Zλ    Var Type ExpZip
    | ZAppL ExpZip Exp
    | ZAppR Exp ExpZip
    | ZType Type ExpZip
    deriving Show


makeArrow :: Type -> Type -> Type
makeArrow dom cod = TApp (TApp (TVar "->") dom) cod
