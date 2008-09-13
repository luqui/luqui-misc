{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Typeable
import Data.Array
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Arrow
import Data.Unique


infixl 9 :*
data Term m where
    TLit :: String -> Term m
    TVar :: String -> Term m
    TAbs :: String -> Term m -> Term m
    (:*) :: Term m -> Term m -> Term m
    -- split x f = f x x
    TSplit :: Term m
    -- destroy x f = f
    TDestroy :: Term m

parensPrec :: Int -> String -> Int -> String
parensPrec p s prec
    | prec > p = "(" ++ s ++ ")"
    | otherwise = s

-- \x. [prec 0]
-- [prec 1] [prec 2]
showTerm :: Term m -> Int -> String
showTerm (TLit s)    = const $ "<" ++ s ++ ">"
showTerm (TVar v)    = const v
showTerm (TAbs v t)  = parensPrec 0 $ "\\" ++ v ++ ". " ++ showTerm t 0
showTerm (f :* x)    = parensPrec 1 $ showTerm f 1 ++ " " ++ showTerm x 2
showTerm TSplit      = const "split"
showTerm TDestroy    = const "destroy"

freeVars :: Term m -> Set.Set String
freeVars (TVar v)    = Set.singleton v
freeVars (TAbs v t)  = Set.delete v (freeVars t)
freeVars (f :* x)    = freeVars f `Set.union` freeVars x
freeVars _           = Set.empty

subst :: String -> Term m -> Term m -> Term m
subst v for e@(TVar v')
    | v == v' = for
    | otherwise = e
subst v for e@(TAbs v' t)
    | v == v' = e
    | otherwise = TAbs v' (subst v for t)
subst v for (f :* x) = subst v for f :* subst v for x
subst v for e = e

type Supply = State Int

fresh :: String -> Supply String
fresh pfx = do
    c <- get
    put $! c+1
    return $ pfx ++ "~" ++ show c

linearize :: Term m -> Supply (Term m)
linearize v@(TVar _) = return v
linearize (TAbs v t) = do
    t' <- linearize t
    return $ if v `Set.member` freeVars t'
             then TAbs v t'
             else TAbs v (TDestroy :* TVar v :* t')
linearize (f :* x) = do
    f' <- linearize f
    x' <- linearize x
    let shared = freeVars f' `Set.intersection` freeVars x'
    elim (Set.toList shared) (f',x')
    where
    elim [] (f,x) = return $ f :* x
    elim (v:vs) (f,x) = do
        v1 <- fresh v
        v2 <- fresh v
        r <- elim vs (subst v (TVar v1) f, subst v (TVar v2) x)
        return $ TSplit :* TVar v :* (TAbs v1 $ TAbs v2 $ r)
linearize e = return e

