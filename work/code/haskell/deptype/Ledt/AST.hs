module Ledt.AST where

import Prelude hiding (pi)

type Var = String

class AST ast where
    -- lambda calculus:
    var :: Var -> ast                -- x
    lam :: Var -> ast -> ast -> ast  -- \x:e₁. e₂
    app :: ast -> ast -> ast         -- e₁ e₂

    -- types
    pi  :: Var -> ast -> ast -> ast  -- (x:e₁ -> e₂)
    set :: Integer    -> ast         -- Set n


data Exp 
    = EVar Var
    | ELam Var Exp Exp
    | EPi  Var Exp Exp
    | EApp Exp Exp 
    | ESet Integer

instance Show Exp where
    show (EVar v) = v
    show (ELam v t b) = "(\\" ++ v ++ ":" ++ show t ++ ". " ++ show b ++ ")"
    show (EApp e e') = "(" ++ show e ++ " " ++ show e' ++ ")"
    show (EPi v t b)
        | free v b  = "(" ++ show t ++ " -> " ++ show b ++ ")"
        | otherwise = "(" ++ v ++ ":" ++ show t ++ " -> " ++ show b ++ ")"
    show (ESet 0) = "Set"
    show (ESet i) = "Set" ++ show i

free :: Var -> Exp -> Bool
free v (EVar v') = v /= v'
free v (ELam v' t b) = free v t && (v == v' || free v b)
free v (EPi v' t b) = free v t && (v == v' || free v b)
free v (EApp e e') = free v e && free v e'
free v (ESet i) = True

instance AST Exp where
    var = EVar
    lam = ELam
    app = EApp
    set = ESet
    pi  = EPi
