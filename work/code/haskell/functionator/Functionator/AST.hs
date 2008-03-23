module Functionator.AST where

type Var = String

data Type
    = TVar Var
    | TΠ   Var  Type
    | TApp Type Type

data Exp
    = EVar  Var
    | Eλ    Var Type Exp
    | EΛ    Var Exp
    | EApp  Exp Exp
    | ETApp Exp Type
    | EType Type Exp
    | EHole

data ExpZip
    = ZTop
    | Zλ    Var Type ExpZip
    | ZΛ    Var ExpZip
    | ZAppL ExpZip Exp
    | ZAppR Exp ExpZip
    | ZTApp ExpZip Type
    | ZType Type ExpZip
