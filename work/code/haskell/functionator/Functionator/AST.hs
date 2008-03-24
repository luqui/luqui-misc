module Functionator.AST where

import Data.Supply
import Control.Monad.Reader

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
    | EHole   Type
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

freeOccurs :: Int -> Type -> Bool
freeOccurs i (TVar v) = False
freeOccurs i (TFree j) = i == j
freeOccurs i (TPi v t) = freeOccurs i t
freeOccurs i (TApp a b) = freeOccurs i a || freeOccurs i b

freeSubstitute :: Supply Int -> Int -> Type -> Type -> Type
freeSubstitute s i t (TFree j) | i == j = t
freeSubstitute s i t (TPi v t') = 
    -- avoiding free variable capture
    let fv = "_t" ++ show (supplyValue s)
    in  TPi fv (freeSubstitute (supplyLeft s) i t
                  (varSubstitute (supplyRight s) v (TVar fv) t'))
freeSubstitute s i t (TApp t1 t2) = 
    TApp (freeSubstitute (supplyLeft  s) i t t1)
         (freeSubstitute (supplyRight s) i t t2)
freeSubstitute _ _ _ t = t

varSubstitute :: Supply Int -> Var -> Type -> Type -> Type
varSubstitute s v t (TVar v') | v == v' = t
varSubstitute s v t (TPi v' t') | v /= v' = 
    -- avoid free variable caputre, as above
    let fv = "_t" ++ show (supplyValue s)
    in  TPi fv (varSubstitute (supplyLeft s) v t
                  (varSubstitute (supplyRight s) v' (TVar fv) t'))
varSubstitute s v t (TApp a b) = 
    TApp (varSubstitute (supplyLeft  s) v t a) 
         (varSubstitute (supplyRight s) v t b)
varSubstitute _ _ _ t = t

integrate :: DExp -> Exp -> Exp
integrate (DLambda v t) e = ELambda v t e
integrate (DAppL r) e = EApp e r
integrate (DAppR l) e = EApp l e
integrate (DType t) e = EType t e

makeArrow :: Type -> Type -> Type
makeArrow dom cod = TApp (TApp (TVar "->") dom) cod

type SExp = Supply Int -> Exp

elam :: (SExp -> SExp) -> SExp
elam f s = 
    let varid   = supplyValue s
        varname = "v" ++ show varid
        fv      = TFree (supplyValue (supplyLeft s))
        body    = f (const $ EVar varname) (supplyRight s)
    in ELambda varname fv body

elam' :: Type -> (SExp -> SExp) -> SExp
elam' t f s = 
    let varid   = supplyValue s
        varname = "v" ++ show varid
        body    = f (const $ EVar varname) (supplyRight s)
    in ELambda varname t body

infixl 9 %
(%) :: SExp -> SExp -> SExp
(%) e e' s = EApp (e (supplyLeft s)) (e (supplyRight s))

etype :: Type -> SExp -> SExp
etype t e s = EType t (e s)

ehole :: SExp
ehole s = EHole $ TFree $ supplyValue s
