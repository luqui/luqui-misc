module Functionator.TypeInfer where

import Functionator.Supply
import Functionator.AST
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

data Equation 
    = Type :~: Type
    deriving Show

type Env = Map.Map Var Type

type Infer a = ReaderT Env (WriterT [Equation] Supply) a

newFree :: Supply Type
newFree = fmap TFree alloc

inferExp :: Exp -> Infer Type
inferExp (EVar v) = asks (Map.! v)
inferExp (ELambda v t e) = do
    etype <- local (Map.insert v t) $ inferExp e
    return $ makeArrow t etype
inferExp (EApp a b) = do
    atype <- inferExp a
    btype <- inferExp b
    adom <- lift $ lift newFree
    acod <- lift $ lift newFree
    tell [ makeArrow adom acod :~: atype ]
    tell [ adom :~: btype ]
    return acod
inferExp (EType t e) = do
    -- XXX need more here, but it's unclear how to make this
    -- work with the introspection procedures.  Putting off
    -- for now.
    etype <- inferExp e
    tell [ etype :~: t ]  -- < this is the wrong line
    return t
inferExp EHole = lift $ lift newFree

type Substitution = Map.Map Int Type

solveEquations :: [Equation] -> Supply Substitution
solveEquations eqs = execStateT (runEquations eqs) Map.empty
    where
    -- instantiate pis
    solve (TPi v t :~: u) = do
        fv <- lift $ lift newFree
        writeEquation (substVar v fv t :~: u)
    solve (t :~: u@(TPi {})) = solve (u :~: t)

    -- instantiate frees
    solve (TFree v :~: TFree w)
        | v == w    = return ()
        | otherwise = writeSubst v (TFree w)
    solve (TFree v :~: t)
        | occurs v t = fail $ "Can't construct infinite type: " ++ show v ++ " = " ++ show t
        | otherwise  = writeSubst v t
    solve (t :~: u@(TFree {})) = solve (u :~: t)

    -- the rest are "opaque"
    solve (TVar v :~: TVar w) | v == w = return ()
    solve (TApp a b :~: TApp c d) = do
        writeEquation (a :~: c)
        writeEquation (b :~: d)

    solve (t :~: u) = fail $ "Can't unify " ++ show t ++ " with " ++ show u

    writeEquation eq = tell [eq]

    writeSubst v t = do
        modify $ Map.map (substFree (Map.singleton v t))
        modify $ Map.insert v t

    occurs i (TFree i') = i == i'
    occurs i (TPi v t) = occurs i t
    occurs i (TApp t u) = occurs i t || occurs i u
    occurs i (TVar v) = False

    substVar v with (TVar v')  | v == v' = with
    substVar v with (TPi v' t) | v /= v' = TPi v' (substVar v with t)
    substVar v with (TApp t u) = TApp (substVar v with t) (substVar v with u)
    substVar v with t = t

    runEquations [] = return ()
    runEquations ((a :~: b):es) = do
        sub <- get
        (_, nexts) <- runWriterT (solve (substFree sub a :~: substFree sub b))
        runEquations $ nexts ++ es

substFree sub (TFree i) = 
    case Map.lookup i sub of
        Just t  -> t
        Nothing -> TFree i
substFree sub (TPi v t) = TPi v (substFree sub t)
substFree sub (TApp t u) = TApp (substFree sub t) (substFree sub u)
substFree sub (TVar v) = TVar v

freeFrees (TVar v) = Set.empty
freeFrees (TFree i) = Set.singleton i
freeFrees (TPi v t) = freeFrees t
freeFrees (TApp a b) = freeFrees a `Set.union` freeFrees b

getHoleCxt :: Env     -- top level environment
           -> ExpZip  -- hole location 
           -> Supply (Type, Type, Env) 
                  -- (top-level type, hole type, hole environment)
getHoleCxt env z = do
    fv <- alloc
    let exp = EType (TFree fv) EHole
    let prog = unzipExp z exp
    (t,eqs) <- runWriterT (runReaderT (inferExp prog) env)
    sub <- solveEquations eqs
    return ( substFree sub t          -- top type
           , substFree sub (TFree fv) -- hole type
           , Map.map (substFree sub) (getHoleEnv z) -- hole environment
           )

getHoleEnv :: ExpZip -> Env
getHoleEnv ZTop = Map.empty
getHoleEnv (ZLambda v t z) = Map.insert v t (getHoleEnv z)
getHoleEnv (ZAppL z r) = getHoleEnv z
getHoleEnv (ZAppR l z) = getHoleEnv z
getHoleEnv (ZType t z) = getHoleEnv z

generalize :: Type -> Supply Type
generalize t = do
    (sub,pfx) <- foldM makeName (Map.empty,id) (Set.elems $ freeFrees t)
    return $ pfx $ substFree sub t
    where
    makeName (sub,pfx) i = do
        nameid <- alloc
        let name = "t" ++ show nameid
        return (Map.insert i (TVar name) sub, TPi name . pfx)

findType :: Env -> Exp -> Supply Type
findType env e = do
    (t,eqs) <- runWriterT (runReaderT (inferExp e) env)
    sub <- solveEquations eqs
    generalize $ substFree sub t
