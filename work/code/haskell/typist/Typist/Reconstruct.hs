{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Reconstruct where

import Typist.AST
import Control.Monad.RWS
import qualified Data.Map as Map

-- From "Colored Local Type Inference"
-- Odersky, Zenger, Zenger, (C) 2001 ACM

data InhT 
    = InhT (Maybe (GenType InhT))
    deriving Show

type Env = Map.Map VarName SynT

type Ann a = RWS Env [Constraint] TypeID a

data Constraint
    = Between SynT (InhT, InhT)


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
        SynT TBottom -> appTpBot
        x -> fail $ "Trying to apply something that doesn't think it's a function: " ++ show x

    generalize ressyn inh
    
    where

    appTp :: ([TypeID], SynT, SynT) -> Ann SynT
    appTp (tvars, dom, rng) = do
        when (length (appTArg app) /= length tvars) $
            fail $ "Can't apply " ++ show (length (appTArg app))
                    ++ " varaibles to a function expecting " ++ show (length tvars)
        ctxtype <- substitute (zip (appTArg app) tvars) dom
        ctx <- destantiate ctxtype
        argtype <- typeAST (appArg app) ctx
        
        substitute (zip (appTArg app) tvars) rng

    appTpBot :: Ann SynT
    appTpBot = do
        typeAST (appArg app) (InhT (Just TTop))
        return (SynT TBottom)

-- rule (app_(tp,_|_))

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


substitute :: [(SynT, TypeID)] -> SynT -> Ann SynT
substitute = undefined
