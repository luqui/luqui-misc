{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Reconstruct (
    makeASTType,
    Constraint(..),
    Type(..),
    TypePad,
) where

import Typist.AST
import Control.Monad.RWS
import qualified Data.Map as Map
import Debug.Trace

type FreeID = Integer

infixr 5 :->

data Type 
    = TInt
    | TBool
    | Type :-> Type
    | TFree FreeID
    deriving (Show, Eq)

data Constraint
    = Type := Type
    deriving Show

data Substitution
    = Type :|-> Type
    deriving Show

type TypePad = Map.Map VarName Type

type Ann a = RWS TypePad [Constraint] FreeID a


makeASTType :: AST -> Type
makeASTType ast = let (typ, cons)    = makeASTTypeConstraint ast
                      subs           = unify cons in
                  lookupFree typ subs

makeASTTypeConstraint :: AST -> (Type, [Constraint])
makeASTTypeConstraint ast = let (typ, _, cons) = runRWS (primTypes $ annotate ast) Map.empty 0 in 
                            (typ, cons)

newFree :: Ann Type
newFree = do
    fid <- get
    put (fid + 1)
    return (TFree fid)

annotate :: AST -> Ann Type

annotate (Lit { litLit = Int { } })  = return TInt
annotate (Lit { litLit = Bool { } }) = return TBool

annotate (Var { varName = var }) = do
    pad <- ask
    if var `Map.member` pad 
        then return $ pad Map.! var
        else fail $ "Undeclared variable: " ++ var

annotate (Lambda { lamParam = param, lamBody = body }) = do
    paramtype <- newFree
    bodytype <- setType param paramtype $ annotate body
    return (paramtype :-> bodytype)

annotate (App { appFun = fun, appArg = arg }) = do
    funtype <- annotate fun
    argtype <- annotate arg
    funleft <- newFree
    funright <- newFree
    tell [funtype := (funleft :-> funright)]
    tell [argtype := funleft]
    return funright

setType :: VarName -> Type -> Ann a -> Ann a
setType var typ = local (Map.insert var typ)

primTypes :: Ann a -> Ann a
primTypes mon = do
    setType "plus" (TInt :-> TInt :-> TInt) $ do
    setType "times" (TInt :-> TInt :-> TInt) $ do
    setType "leq" (TInt :-> TInt :-> TBool) $ do
    ifa <- newFree
    setType "if" (TBool :-> ifa :-> ifa :-> ifa) $ do
    setType "True" TBool $ do
    setType "False" TBool $ do
    fixa <- newFree
    setType "fix" ((fixa :-> fixa) :-> fixa) $ mon

substitute :: Substitution -> Type -> Type
substitute sub (a :-> b) = substitute sub a :-> substitute sub b
substitute (from :|-> to) free@(TFree {}) = 
    if from == free
        then to
        else free
substitute _ x = x

substituteConstraint :: Substitution -> Constraint -> Constraint
substituteConstraint sub (a := b) = substitute sub a := substitute sub b

(|->) :: Type -> Type -> [Constraint] -> [Constraint]
(|->) s t = map (substituteConstraint (s :|-> t))

frees :: Type -> [Type]
frees (a :-> b)  = frees a ++ frees b
frees f@(TFree {}) = [f]
frees _            = []

lookupFree :: Type -> [Substitution] -> Type
lookupFree = foldl (flip substitute)

-- Straight from TaPL, page 327
unify :: [Constraint] -> [Substitution]
unify [] = []
unify ((s := t):c')
    | s == t                 = unify(c')
    | TFree {} <- s
    , not (s `elem` frees t) = (s :|-> t) : unify ((s |-> t) c')
    | TFree {} <- t
    , not (t `elem` frees s) = (t :|-> s) : unify ((t |-> s) c')
    | s1 :-> s2 <- s
    , t1 :-> t2 <- t         = unify (c' ++ [s1 := t1, s2 := t2])
    | otherwise              = error $ "Error when unifying " ++ show s ++ " and " ++ show t
