module TypeInfer
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

getType :: AST -> Type
getType (Type t _) = t
getType _ = error "getType on a type-unannotated node"

annotate :: AST -> Reconstruct AST
annotate (App f arg) = do
    fast   <- annotate f
    argast <- annotate arg
    fta <- makeVar
    ftb <- makeVar
    tell [(getType fast, TArrow fta ftb)]
    tell [(getType argast, fta)]
    return $ Type ftb (App fast argast)
    
annotate (Lam var body) = do
    vartype <- makeVar
    bodyast <- local (Map.insert var vartype) $ annotate body
    return $ Type (TArrow vartype (getType bodyast)) (Lam var bodyast)

annotate (Var var) = do
    t <- Map.lookup var =<< ask
    return $ Type t (Var var)
annotate ast@(Lit (LInt _))   = return $ Type (TAtom "Int")   ast
annotate ast@(Lit (LFloat _)) = return $ Type (TAtom "Float") ast
annotate ast@(Lit (LStr _))   = return $ Type (TAtom "Str")   ast

annotate (Type t ast) = do
    ann <- annotate ast
    tell [(getType ann, t), (t, getType ann)]
    return ann
    
annotate Hole             = do
    t <- makeVar
    return $ Type t Hole

annotate (Builtin (BTuple xs))  = do
    asts <- mapM annotate xs
    return $ Type (TTuple (map getType asts)) (Builtin (BTuple asts))
annotate (Builtin (BTag t x))   = do
    ast <- annotate x
    return $ Type (TUnion [(t, getType ast)]) ast

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
                              . filter (\eq -> snd eq == TVar var && isConcrete (fst eq))
                              $ eqs

upperBoundType :: [Equation] -> Type -> Type
upperBoundType eqs x@(TAtom {}) = x
upperBoundType eqs (TArrow a b) = TArrow (lowerBoundType eqs a) (upperBoundType eqs b)
upperBoundType eqs (TTuple as) = TTuple $ map (upperBoundType eqs) as
upperBoundType eqs (TUnion as) = TUnion $ map (\(v,t) -> (v, upperBoundType eqs t)) as  -- not sure about this one
upperBoundType eqs (TVar var) = foldr typeInf (TAtom "Top") 
                              . map snd 
                              . filter (\eq -> fst eq == TVar var && isConcrete (snd eq))
                              $ eqs

boundType :: [Equation] -> Type -> (Type,Type)
boundType eqs t = (lowerBoundType eqs t, upperBoundType eqs t)
