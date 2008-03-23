module Functionator.AST where

import Functionator.Supply
import Control.Monad

type Var = String

data Type
    = TVar  Var
    | TFree Int
    | TPi   Var Type
    | TApp  Type Type

instance Show Type where
    show (TVar v) = v
    show (TFree i) = "^" ++ show i
    show (TPi v t) = "\\/" ++ v ++ ". " ++ show t
    show (TApp (TApp (TVar "->") a) b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TApp a b) = "(" ++ show a ++ " " ++ show b ++ ")"

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

elam :: (Supply Exp -> Supply Exp) -> Supply Exp
elam f = do
    varid <- alloc
    let varname = "v" ++ show varid
    fv    <- liftM TFree alloc
    body  <- f (return $ EVar varname)
    return $ ELambda varname fv body

elam' :: Type -> (Supply Exp -> Supply Exp) -> Supply Exp
elam' t f = do
    varid <- alloc
    let varname = "v" ++ show varid
    body <- f (return $ EVar varname)
    return $ ELambda varname t body

eapp :: Supply Exp -> Supply Exp -> Supply Exp
eapp e e' = liftM2 EApp e e'

etype :: Type -> Supply Exp -> Supply Exp
etype t e = liftM (EType t) e

ehole :: Supply Exp
ehole = return EHole
