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
    | ZLambda Var Type ExpZip
    | ZAppL   ExpZip Exp
    | ZAppR   Exp ExpZip
    | ZType   Type ExpZip
    deriving Show

alphaEquiv :: Type -> Type -> Supply Bool
alphaEquiv (TVar v) (TVar w)     = return $ v == w
alphaEquiv (TFree i) (TFree j)   = return $ i == j
alphaEquiv (TPi v t) (TPi v' t') = do
    -- XXX need support for reordering of pis
    fv <- liftM TFree alloc
    alphaEquiv (typeSubstVar v fv t) (typeSubstVar v' fv t')
alphaEquiv (TApp a b) (TApp a' b') = do
    c1 <- alphaEquiv a a'
    if not c1
       then return False
       else alphaEquiv b b'

typeSubstVar :: String -> Type -> Type -> Type
typeSubstVar v with t = 
    case t of
         TVar v'  | v == v' -> with
         TPi v' b | v /= v' -> TPi v' (typeSubstVar v with b)
         TApp t u           -> TApp (typeSubstVar v with t) (typeSubstVar v with u)
         t                  -> t

unzipExp :: ExpZip -> Exp -> Exp
unzipExp ZTop e = e
unzipExp (ZLambda v t z) e = unzipExp z (ELambda v t e)
unzipExp (ZAppL z r) e = unzipExp z (EApp e r)
unzipExp (ZAppR l z) e = unzipExp z (EApp l e)
unzipExp (ZType t z) e = unzipExp z (EType t e)

findHoles :: Exp -> [ExpZip]
findHoles e = findHoles' e ZTop
    where
    findHoles' (EVar v) cx = []
    findHoles' (ELambda v t e) cx = findHoles' e (ZLambda v t cx)
    findHoles' (EApp a b) cx = findHoles' a (ZAppL cx b) 
                            ++ findHoles' b (ZAppR a cx)
    findHoles' (EType t e) cx = findHoles' e (ZType t cx)
    findHoles' EHole cx = [cx]

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
