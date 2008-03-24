module Functionator.Pointer where

import Data.Supply
import Functionator.AST
import qualified Data.Map as Map

data Pointer
    = Pointer { pEnv :: Map.Map Var Type
              , pCxt :: ExpCxt
              , pExp :: Exp
              }

instance Show Pointer where
    show p = show (pCxt p) ++ " |- " ++ show (pExp p)

freeSubstitutePointer :: Supply Int -> Int -> Type -> Pointer -> Pointer
freeSubstitutePointer s i t p =
    Pointer { pEnv  = snd $ Map.mapAccum accumFunc s1 (pEnv p)
            , pCxt  = freeSubstituteExpCxt s2 i t (pCxt p)
            , pExp  = freeSubstituteExp s3 i t (pExp p)
            }
    where
    s1:s2:s3:_ = split s
    accumFunc s v = (supplyLeft s, freeSubstitute (supplyRight s) i t v)


unify :: Supply Int -> Type -> Type -> Pointer -> Pointer
unify s (TFree i) (TFree j) p | i == j = p
unify s (TFree i) t p | not (freeOccurs i t) = freeSubstitutePointer s i t p
unify s t (TFree i) p | not (freeOccurs i t) = freeSubstitutePointer s i t p
unify s (TPi v body) t p = 
    let fv = TFree (supplyValue s)
    in unify (supplyLeft s) (varSubstitute (supplyRight s) v fv body) t p
unify s t t'@(TPi {}) p = unify s t' t p
unify s (TVar v) (TVar v') p | v == v'   = p
unify s (TApp a b) (TApp a' b') p = 
    unify (supplyLeft s) a a' $ unify (supplyRight s) b b' p
unify _ a b _ = error $ "Can't unify " ++ show a ++ " with " ++ show b

newPointer :: Map.Map Var Type -> Type -> Pointer
newPointer env typ =
    Pointer { pEnv = env
            , pCxt = []
            , pExp = EHole typ
            }

makeApp :: Supply Int -> Pointer -> Pointer
makeApp s p
    | EHole resultType <- pExp p =
        let s1:s2:_ = split s
            t1 = TFree (supplyValue s1)
            t2 = TFree (supplyValue s2)
        in p { pExp = EApp (EHole (makeArrow t1 resultType)) (EHole t2) }
    | otherwise = error $ "Expression not empty: " ++ show (pExp p)

makeLambda :: Supply Int -> Var -> Pointer -> Pointer
makeLambda s v p
    | EHole resultType <- pExp p =
        let s1:s2:s3:_ = split s
            t1 = TFree (supplyValue s1)
            t2 = TFree (supplyValue s2)
        in unify s3 (makeArrow t1 t2) resultType $ 
                p { pExp = ELambda v t1 (EHole t2) }
    | otherwise = error $ "Expression not empty: " ++ show (pExp p)

makeVar :: Supply Int -> Var -> Pointer -> Pointer
makeVar s v p
    | Just varType <- Map.lookup v (cxtEnv (pCxt p) `Map.union` pEnv p)
    , EHole resultType <- pExp p =
        unify s varType resultType $ p { pExp = EVar v }
    | otherwise = error $ "Expression not empty (" ++ show (pExp p)
                       ++ ") or variable (" ++ show v ++ ") not in environment"

cxtEnv :: ExpCxt -> Map.Map Var Type
cxtEnv (DLambda v t : cxs) = Map.insert v t (cxtEnv cxs)
cxtEnv (_ : cxs)     = cxtEnv cxs

goAppL :: Pointer -> Pointer
goAppL p
    | EApp l r <- pExp p = p { pExp = l, pCxt = DAppL r : pCxt p }
    | otherwise = error "Not an App"

goAppR :: Pointer -> Pointer
goAppR p
    | EApp l r <- pExp p = p { pExp = r, pCxt = DAppR l : pCxt p }
    | otherwise = error "Not an App"

goLambda :: Pointer -> Pointer
goLambda p
    | ELambda v t e <- pExp p =  
        p { pExp = e, pCxt = DLambda v t : pCxt p }
    | otherwise = error "Not a Lambda"
