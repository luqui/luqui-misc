module Ledt.Exp where

import Prelude hiding (pi)
import Ledt.AST
import Control.Monad.State
import Control.Applicative

data Var
    = VarNamed String
    | VarFree  Integer
    deriving Eq

data Exp 
    = EVar Var
    | ELam Var Exp Exp
    | EPi  Var Exp Exp
    | EApp Exp Exp 
    | ESet Integer

instance Show Exp where
    show = showExp pNone

newtype ExpMonad a = ExpMonad (State Integer a)
    deriving (Functor, Monad, MonadState Integer)

genExp :: ExpMonad Exp -> Exp
genExp (ExpMonad m) = evalState m 1

newFree :: ExpMonad Var
newFree = do
    i <- get
    put $! succ i
    return $ VarFree i

newVar :: ExpMonad Var
newVar = do
    i <- get
    put $! succ i
    return $ VarNamed ("v" ++ show i)

instance AST (ExpMonad Exp) where
    lam typ fn = do
        v <- newVar
        (ELam v <$> typ) `ap` fn (return (EVar v))
    pi typ fn = do
        v <- newVar
        (EPi v <$> typ) `ap` fn (return (EVar v))
    (%) = liftM2 EApp
    set = return . ESet

instance ASTInfer (ExpMonad Exp) where
    lam_ fn = lam (EVar <$> newFree) fn
    pi_ fn = pi (EVar <$> newFree) fn

pparen :: Bool -> String -> String
pparen False str = str
pparen True  str = "(" ++ str ++ ")"

showVar :: Var -> String
showVar (VarNamed n)  = n
showVar (VarFree n)   = "*" ++ show n

data Paren 
    = Paren { parenApp   :: Bool
            , parenArr   :: Bool
            , parenLam   :: Bool
            }

pNone = Paren False False False
pApps = Paren True False False
pArrs = Paren False True False
pLams = Paren False False True
pAll  = Paren True True True

(Paren a b c) .+ (Paren a' b' c') = Paren (a||a') (b||b') (c||c')

showExp :: Paren -> Exp -> String
showExp p (EVar v)          = showVar v
showExp p (ELam v typ body) = 
    pparen (parenLam p)
              $ "\\"  ++ showVar v 
              ++ ":"  ++ showExp pAll typ
              ++ ". " ++ showExp pNone body
showExp p (EPi v typ body)
    | free v body = pparen (parenArr p) $ 
            "(" ++ showVar v ++ " : " ++ showExp pNone typ ++ ")"
                ++ " -> " ++ showExp pNone body
    | otherwise = pparen (parenArr p) 
              $ showExp (pArrs .+ pLams) typ ++ " -> " ++ showExp pNone body
showExp p (EApp a b) = 
    pparen (parenApp p) $ showExp (pLams .+ pArrs) a ++ " " ++ showExp pAll b
showExp p (ESet n)
    | n == 0    = "Set"
    | otherwise = "Set" ++ show n


free :: Var -> Exp -> Bool
free x (EVar y) = x == y
free x (ELam v typ body) = free x typ || (x /= v && free x body)
free x (EPi  v typ body) = free x typ || (x /= v && free x body)
free x (EApp a b) = free x a || free x b
free x (ESet _)   = False
