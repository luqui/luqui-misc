{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Reconstruct where

import Typist.AST
import Debug.Trace

data Type
    = Type :-> Type
    | TInt
    | TBool
    deriving (Eq,Show)

type Gamma = [(VarName, Type -> (Delta,Type))]
type Delta = [(VarName, Type)]

popGamma :: (Eq a, Show a, Show b) => a -> [(a,b)] -> [(a,b)]
popGamma a [] = []
popGamma a ((x,y):xs) = 
    if a == x
        then xs
        else (x,y) : popGamma a xs

lookupRemove :: (Eq a) => a -> [(a,b)] -> Maybe (b, [(a,b)])
lookupRemove a [] = Nothing
lookupRemove a ((x,y):xs) =
    if a == x
        then Just (y, xs)
        else do (ret, rest) <- lookupRemove a xs
                return (ret, (x,y):rest)

typeOf :: AST -> Gamma -> Type -> (Delta,Type)

typeOf (Lit { litLit = Int {}})  _ _ = ([], TInt)
typeOf (Lit { litLit = Bool {}}) _ _ = ([], TBool)

typeOf (App { appFun = fun, appArg = arg }) gamma cxt =
    let (delta1, ~(fundom :-> funrng)) = typeOf fun gamma (argtype :-> cxt)
        (delta2, argtype) = typeOf arg gamma fundom in
    (unify delta1 delta2, funrng)

typeOf (Lambda { lamParam = param, lamBody = body }) gamma ~(dom :-> rng) =
    let gamma' = (param, \cx -> ([(param, cx)], dom)) : gamma
        (delta, trng) = typeOf body gamma' rng in
    (popGamma param delta, 
     maybe dom id (lookup param delta) :-> trng)

typeOf (Var { varName = name }) gamma cxt =
    maybe (error $ "Undeclared variable: " ++ name)
          ($ cxt)
          (lookup name gamma)

unify :: Delta -> Delta -> Delta
unify [] bs = bs
unify ((x,y):as) bs = 
    maybe ((x,y) : unify as bs)
          (\ (t,rest) -> (x, singleUnify t y) : unify as rest)
          (lookupRemove x bs)

singleUnify :: Type -> Type -> Type
singleUnify x y = 
    if x == y
        then x
        else error $ "Type Error when unifying " ++ show x ++ " and " ++ show y
