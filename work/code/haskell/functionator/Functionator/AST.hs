module Functionator.AST where

import Functionator.Supply
import Control.Monad

type Var = String

data Type
    = TVar  Var
    | TFree Int
    | TPi   Var Type
    | TApp  Type Type

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

updateCxt :: ExpCxt -> Exp -> ExpCxt -> Maybe ExpCxt
updateCxt loc repl target = fmap reverse $ merge' (reverse loc) (reverse target)
    where
    merge' _  [] = Nothing  -- entered my hole!
    merge' [] _  = Nothing  -- replaced a parent node of mine
       -- could compare for equality, but why
    merge' (DLambda v t : xs) (DLambda v' t' : ys) = fmap (DLambda v t :) $ merge' xs ys
    merge' (DAppL e : xs)     (DAppL e' : ys)      = fmap (DAppL e' :)    $ merge' xs ys
    merge' (DAppR e : xs)     (DAppR e' : ys)      = fmap (DAppR e' :)    $ merge' xs ys
    merge' (DType t : xs)     (DType t' : ys)      = fmap (DType t :)     $ merge' xs ys

    merge' (DAppL re : xs) (DAppR le : ys) = Just $ DAppR (unzipExp (reverse xs) repl) : ys
    merge' (DAppR le : xs) (DAppL re : ys) = Just $ DAppL (unzipExp (reverse xs) repl) : ys

    merge' _ _ = error "Two contexts are not compatible during merge"

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
