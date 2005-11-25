{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Reconstruct where

import Typist.AST
import Control.Monad.RWS
import qualified Data.Map as Map
import Debug.Trace

-- From "Colored Local Type Inference"
-- Odersky, Zenger, Zenger, (C) 2001 ACM

-- Constraint solving from "Local Type Inference"
-- Pierce, Turner,  1997

data InhT 
    = InhT (Maybe (GenType InhT))
    deriving Show

type Env = Map.Map VarName SynT

type Ann a = RWS Env () TypeID a

data Bound
    = Bound SynT SynT
    deriving Show

type Constraints = Map.Map TypeID Bound

data Substitution 
    = Substitute TypeID SynT
    deriving Show


-- LTI page 4
(<:) :: SynT -> SynT -> Bool
(SynT (TVar a)) <: (SynT (TVar b))  = a == b
_ <: (SynT TTop)                    = True
(SynT TBot) <: _                    = True

(SynT (TFunc fvars fdom frng)) <: (SynT (TFunc gvars gdom grng)) =
    | length fvars == length gvars = 
        let subs = substitute (zipWith Substitute gvars (map (SynT . TVar) fvars)) in
        subs gdom <: fdom  &&  frng <: subs grng

(SynT TInt)  <: (SynT TInt)         = True
(SynT TBool) <: (SynT TBool)        = True
_ <: _                              = False


newFree :: Ann SynT
newFree = do
    varnum <- get
    put (varnum + 1)
    return $ SynT (TVar varnum)


-- This function implements the algorithm on page 11 of CLTI
typeAST :: AST -> InhT -> Ann SynT

-- rule (var)
typeAST (Var { varName = name }) inh = do
    env <- ask
    if name `Map.member` env 
        then generalize (env Map.! name) inh
        else fail $ "Undeclared variable: " ++ name

-- rule (abs_(tp, ?))
typeAST lam@(ExpLambda {})
        (InhT Nothing) = do
    bodytype <- local (Map.insert (lamParam lam) (lamParamT lam)) $
                    typeAST (lamBody lam) (InhT Nothing)
    return $ SynT $ TFunc (lamTParam lam) (lamParamT lam) bodytype

-- rule (abs_(tp, T))
typeAST lam@(ExpLambda {})
        (InhT (Just TTop)) = do
    bodytype <- local (Map.insert (lamParam lam) (lamParamT lam)) $
                    typeAST (lamBody lam) (InhT (Just TTop))
    return $ SynT $ TTop

-- rule (abs_tp)
typeAST lam@(ExpLambda {})
        inh@(InhT (Just (TFunc tvars dom rng))) = do
    bodytype <- local (Map.insert (lamParam lam) (lamParamT lam)) $
                    typeAST (lamBody lam) rng
    generalize (SynT $ TFunc tvars (lamParamT lam) bodytype) inh

-- rule (abs)
typeAST lam@(Lambda {})
        inh@(InhT (Just (TFunc tvars dom rng))) = do
    syndom <- instantiate dom
    bodytype <- local (Map.insert (lamParam lam) syndom) $
                    typeAST (lamBody lam) rng
    return $ SynT $ TFunc tvars syndom bodytype
    
-- rule (app_tp) and (app_(tp,_|_))
typeAST app@(ExpApp {})
        inh = do
    funtype <- typeAST (appFun app) (InhT Nothing)
    ressyn <- case funtype of
        SynT (TFunc tvars dom rng) -> appTp (tvars,dom,rng)
        SynT TBot -> appTpBot
        x -> fail $ "Trying to apply something that doesn't think it's a function: " ++ show x

    generalize ressyn inh
    
    where

    appTp :: ([TypeID], SynT, SynT) -> Ann SynT
    appTp (tvars, dom, rng) = do
        when (length (appTArg app) /= length tvars) $
            fail $ "Can't apply " ++ show (length (appTArg app))
                    ++ " varaibles to a function expecting " ++ show (length tvars)
        let ctxtype = substitute (zipWith Substitute tvars (appTArg app)) dom
        ctx <- destantiate ctxtype
        argtype <- typeAST (appArg app) ctx
        
        return $ substitute (zipWith Substitute tvars (appTArg app)) rng

    appTpBot :: Ann SynT
    appTpBot = do
        typeAST (appArg app) (InhT (Just TTop))
        return (SynT TBot)

-- rule (app) and (app_|_)
 

typeAST ast inh = fail $ "Can't type (" ++ show ast ++ ") with context (" ++ show inh ++ ")"




-- take an InhT pattern and create a type out of it
-- what to do when the pattern has holes??
instantiate :: InhT -> Ann SynT
instantiate = undefined

-- take a SynT type and create a fully defined InhT
-- pattern
destantiate :: SynT -> Ann InhT
destantiate = undefined

-- The up-right arrow operation in the paper
-- Match a SynT against an InhT pattern covariantly
generalize :: SynT -> InhT -> Ann SynT
generalize = undefined

-- The down-right arrow operation in the paper
-- Match a SynT against an InhT pattern contravariantly
specify :: SynT -> InhT -> Ann SynT
specify = undefined


substitute :: [Substitution] -> SynT -> SynT
substitute ss t
    | trace ("sub " ++ show ss ++ " in " ++ show t) False = undefined
substitute [] t = t
substitute ((Substitute src dest):ss) v@(SynT (TVar x)) 
    | x == src  =  substitute ss dest
    | otherwise =  substitute ss v
substitute ss (SynT (TFunc vars dom rng)) =
    -- XXX remove vars from ss?
    SynT (TFunc vars (substitute ss dom) (substitute ss rng))
substitute ss x = x


-- least upper bound of two types   (LTI page 5)
sup :: SynT -> SynT -> SynT
sup = undefined

-- greatest lower bound of two types
inf :: SynT -> SynT -> SynT
inf = undefined

