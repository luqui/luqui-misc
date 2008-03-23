module Functionator.TypeInfer where

import Functionator.AST
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

data Equation 
    = Type :~: Type
    deriving Show

type Env = Map.Map Var Type

newtype Supply a = Supply (State Int a)
    deriving (Functor, Monad)

type Infer a = ReaderT Env (WriterT [Equation] Supply) a

newFree :: Supply Type
newFree = Supply $ do
    ret <- get
    put $! ret+1
    return $ TFree ret

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
    etype <- inferExp e
    tell [ etype :~: t ]
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
        | occurs v t  = fail $ "Can't construct infinite type: " ++ show v ++ " = " ++ show t
        | otherwise = writeSubst v t
    solve (t :~: u@(TFree {})) = solve (u :~: t)

    -- the rest are "opaque"
    solve (TVar v :~: TVar w) | v == w = return ()
    solve (TApp a b :~: TApp c d) = do
        writeEquation (a :~: c)
        writeEquation (b :~: d)

    solve (t :~: u) = fail $ "Can't unify " ++ show t ++ " with " ++ show u

    writeEquation eq = tell [eq]

    writeSubst v t = modify (Map.insert v t)

    occurs i (TFree i') = i == i'
    occurs i (TPi v t) = occurs i t
    occurs i (TApp t u) = occurs i t || occurs i u
    occurs i (TVar v) = False

    substVar v with (TVar v')  | v == v' = with
    substVar v with (TPi v' t) | v /= v' = TPi v' (substVar v with t)
    substVar v with (TApp t u) = TApp (substVar v with t) (substVar v with u)
    substVar v with t = t

    substFree sub (TFree i) = 
        case Map.lookup i sub of
            Just t  -> t
            Nothing -> TFree i
    substFree sub (TPi v t) = TPi v (substFree sub t)
    substFree sub (TApp t u) = TApp (substFree sub t) (substFree sub u)
    substFree sub (TVar v) = TVar v

    runEquations [] = return ()
    runEquations ((a :~: b):es) = do
        sub <- get
        (_, nexts) <- runWriterT (solve (substFree sub a :~: substFree sub b))
        runEquations $ nexts ++ es
