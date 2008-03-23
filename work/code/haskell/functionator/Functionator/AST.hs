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

data DExp
    = DLambda Var Type
    | DAppL   Exp
    | DAppR   Exp
    | DType   Type
    deriving Show

type ExpCxt = [DExp]

unzipExp :: ExpCxt -> Exp -> Exp
unzipExp cx e = foldl (\es dexp -> integrate dexp es) e cx

integrate :: DExp -> Exp -> Exp
integrate (DLambda v t) e = ELambda v t e
integrate (DAppL r) e = EApp e r
integrate (DAppR l) e = EApp l e
integrate (DType t) e = EType t e

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

infixl 9 %
(%) :: Supply Exp -> Supply Exp -> Supply Exp
(%) e e' = liftM2 EApp e e'

etype :: Type -> Supply Exp -> Supply Exp
etype t e = liftM (EType t) e

ehole :: Supply Exp
ehole = return EHole
