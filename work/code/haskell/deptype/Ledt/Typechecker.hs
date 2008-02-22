module Ledt.Typechecker where

import Prelude hiding (pi)
import Ledt.AST

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as Map

type Val = Exp
type TypeEnv = Map.Map Var Val
type ValEnv  = Map.Map Var Val
type TypeError = String
type FreshVar = Int

newtype TC a = TC { unTC :: ReaderT TypeEnv (StateT FreshVar (ErrorT TypeError Identity)) a }
    deriving (Functor, Monad, MonadReader TypeEnv, MonadState FreshVar, MonadError TypeError)

runTC :: TC a -> a
runTC (TC m) = fromRight $ runIdentity $ runErrorT $ evalStateT (runReaderT m Map.empty) 0
    where
    fromRight (Left err) = error err
    fromRight (Right a) = a

instance Applicative TC where
    pure = return
    (<*>) = ap

newVar :: TC Var
newVar = do
    vn <- get
    put $! vn + 1
    return ("_" ++ show vn)

alphaConv :: Var -> Var -> Exp -> Exp
alphaConv inv outv (EVar v)
    | inv  == v  = EVar outv
    | outv == v  = error "alpha converting to non-fresh variable"
    | otherwise  = EVar v
alphaConv inv outv (ELam v typ body)
    | inv  == v  = ELam v (alphaConv inv outv typ) body
    | outv == v  = error "alpha converting to non-fresh variable"
    | otherwise  = ELam v (alphaConv inv outv typ) (alphaConv inv outv body)
alphaConv inv outv (EPi v typ body)
    | inv  == v  = EPi  v (alphaConv inv outv typ) body
    | outv == v  = error "alpha converting to a non-fresh variable"
    | otherwise  = EPi  v (alphaConv inv outv typ) (alphaConv inv outv body)
alphaConv inv outv (EApp e e')
                 = EApp (alphaConv inv outv e) (alphaConv inv outv e')
alphaConv inv outv (ESet i) 
                 = ESet i

betaConv :: Var -> Exp -> Exp -> TC Exp
betaConv v val (EVar v')
    | v == v'   = return val
    | otherwise = return $ EVar v'
betaConv v val (ELam v' typ body) = do
    fresh <- newVar
    btyp <- betaConv v val typ
    let val' = alphaConv v' fresh val
    bbody <- betaConv v val' body
    return $ ELam v' btyp bbody
betaConv v val (EPi v' typ body) = do
    fresh <- newVar
    btyp <- betaConv v val typ
    let val' = alphaConv v' fresh val
    bbody <- betaConv v val' body
    return $ EPi v' btyp bbody
betaConv v val (EApp e e') = do
    be  <- betaConv v val e
    be' <- betaConv v val e'
    return $ EApp be be'
betaConv v val (ESet i) = return $ ESet i

eval :: Exp -> TC Val
eval (EApp e e') = do
    ELam var typ body <- eval e
    -- where did typ go?
    betaConv var e' body
eval e = return e

equal :: Exp -> Exp -> TC Bool
equal e e' = do
    be  <- eval e
    be' <- eval e'
    equal' be be'
    where
    equal' (EVar v) (EVar v') = return $ v == v'
    -- Note how there is no ELam case.  That's an intuitive decision:
    -- we don't check alpha equality of lambdas, just pis.  If not 
    -- enough programs are typechecking, try adding this case.
    equal' (EPi v typ body) (EPi v' typ' body') = do
        typEq  <- equal typ typ'
        fresh  <- newVar
        bodyEq <- equal (alphaConv v fresh body) (alphaConv v' fresh body')
        return $ typEq && bodyEq
    equal' (ESet i) (ESet i') = return $ i == i'
    equal' _ _ = return False

typecheck :: Exp -> TC Val
typecheck (EVar v) = Map.lookup v =<< ask
typecheck (ELam v typ body) = do
    order typ >> typecheck typ
    bodytyp <- local (Map.insert v typ) $ typecheck body
    return $ EPi v typ bodytyp
typecheck (EPi v typ body) = do
    order typ
    typord <- order =<< typecheck typ
    bodyord <- order =<< local (Map.insert v typ) (typecheck body)
    return $ ESet (max typord bodyord)
typecheck (EApp e e') = do
    EPi v typ body <- eval =<< typecheck e
    etype' <- typecheck e'
    eql <- equal typ etype'
    when (not eql) $ 
        fail $ "Type error: " ++ show typ ++ " /= " ++ show etype'
    betaConv v e' body
typecheck (ESet n) = return $ ESet (n+1)

order :: Exp -> TC Integer
order e = do
    e' <- eval e
    order' e'
    where
    order' (EVar v) = do
        ty <- eval =<< Map.lookup v =<< ask
        case ty of
             ESet _ -> return 0
             _      -> fail $ v ++ " is not necessarily a type, when checking its universe order"
    order' l@(ELam {}) = fail $ show l ++ " is not a type, when trying to check its universe order"
    order' (EPi v typ body) = succ <$> (max <$> order typ <*> local (Map.insert v typ) (order body))
    order' (EApp {}) = fail "That's impossible, eval was supposed to reduce to WHNF or not terminate!"
    order' (ESet i) = return i
