module Reconstruct
    (
    )
where

import AST
import Type

import Control.Monad.RWS
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

import Debug.Trace

type TypeEnv = Map.Map Var Type
type Equation = (Type, Type)
type Reconstruct a = RWS TypeEnv [Equation] Integer a

makeVar :: Reconstruct Type
makeVar = do
    ret <- get
    put (ret+1)
    return (TVar ret)

typeVarOf :: AST -> Reconstruct Type
typeVarOf (App f arg) = do
    ftype   <- typeVarOf f
    argtype <- typeVarOf arg
    fta <- makeVar
    ftb <- makeVar
    tell [(ftype, TArrow fta ftb)]
    tell [(argtype, fta)]
    return ftb
typeVarOf (Lam var body) = do
    vartype <- makeVar
    bodytype <- local (Map.insert var vartype) $ typeVarOf body
    return $ TArrow vartype bodytype
typeVarOf (Var var) = do
    Map.lookup var =<< ask
typeVarOf (Lit (LInt _))   = return $ TAtom "Int"
typeVarOf (Lit (LFloat _)) = return $ TAtom "Float"
typeVarOf (Lit (LStr _))   = return $ TAtom "Str"
typeVarOf (Type t _)       = return t
typeVarOf Hole             = makeVar

type Solver a = State (Set.Set Equation) a

(<<) :: Monad m => m a -> m b -> m a
(<<) = flip (>>)

reduceEquations :: [Equation] -> [Equation]
reduceEquations eqs = Set.toList $ execState (mapM_ addEquation eqs) Set.empty
    where
    addEquation :: Equation -> Solver ()
    addEquation eq = do
        cur <- get
        if eq `Set.member` cur
            then return ()
            else modify (Set.insert eq) >> transformEquation eq

    transformEquation :: Equation -> Solver ()
    transformEquation ((TArrow a b), (TArrow a' b'))
        = mapM_ addEquation [(a',a), (b,b')]
    transformEquation (a, b) = do
        case a of
            TVar a' -> get >>= Set.fold (\eq m -> m << case eq of
                                            (x, TVar y') | y' == a' -> addEquation (x,b)
                                            _                       -> return ()) (return ())
            _       -> return ()
        case b of
            TVar b' -> get >>= Set.fold (\eq m -> m << case eq of
                                            (TVar x', y) | x' == b' -> addEquation (a,y)
                                            _                       -> return ()) (return ())
            _       -> return ()

isConcrete :: Type -> Bool
isConcrete (TAtom {}) = True
isConcrete (TArrow a b) = isConcrete a && isConcrete b
isConcrete (TTuple as) = all isConcrete as
isConcrete (TUnion as) = all isConcrete $ map snd as
isConcrete (TVar {}) = False

lowerBoundType :: [Equation] -> Type -> Type
lowerBoundType eqs x@(TAtom {}) = x
lowerBoundType eqs (TArrow a b) = TArrow (upperBoundType eqs a) (lowerBoundType eqs b)
lowerBoundType eqs (TTuple as) = TTuple $ map (lowerBoundType eqs) as
lowerBoundType eqs (TUnion as) = TUnion $ map (\(v,t) -> (v, lowerBoundType eqs t)) as  -- not sure about this one
lowerBoundType eqs (TVar var) = foldr typeSup (TAtom "Bot") 
                              . map fst 
                              . filter (\eq -> snd eq == TVar var && isConcrete (fst eq)
                                        && trace ("Considering " ++ show (fst eq) ++ " for lower bound of " ++ show (TVar var)) True)
                              $ eqs

upperBoundType :: [Equation] -> Type -> Type
upperBoundType eqs x@(TAtom {}) = x
upperBoundType eqs (TArrow a b) = TArrow (lowerBoundType eqs a) (upperBoundType eqs b)
upperBoundType eqs (TTuple as) = TTuple $ map (upperBoundType eqs) as
upperBoundType eqs (TUnion as) = TUnion $ map (\(v,t) -> (v, upperBoundType eqs t)) as  -- not sure about this one
upperBoundType eqs (TVar var) = foldr typeInf (TAtom "Top") 
                              . map snd 
                              . filter (\eq -> fst eq == TVar var && isConcrete (snd eq)
                                        && trace ("Considering " ++ show (snd eq) ++ " for upper bound of " ++ show (TVar var)) True)
                              $ eqs

boundType :: [Equation] -> Type -> (Type,Type)
boundType eqs t = (lowerBoundType eqs t, upperBoundType eqs t)
