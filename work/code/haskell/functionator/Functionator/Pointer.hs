module Functionator.Pointer where

import Data.Supply
import Functionator.AST
import qualified Data.Map as Map

data Pointer
    = Pointer { pEnv :: Map.Map Var Type
              , pCxt :: ExpCxt
              , pExp :: Exp
              , pType :: Type
              }

freeSubstitutePointer :: Supply Int -> Int -> Type -> Pointer -> Pointer
freeSubstitutePointer s i t p =
    Pointer { pEnv  = snd $ Map.mapAccum accumFunc s1 (pEnv p)
            , pCxt  = freeSubstituteExpCxt s2 i t (pCxt p)
            , pExp  = freeSubstituteExp s3 i t (pExp p)
            , pType = freeSubstitute s4 i t (pType p)
            }
    where
    s1:s2:s3:s4:_ = split s
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
unify s (TApp a b) (TApp a' b') p = unify (supplyLeft s) a a' $ unify (supplyRight s) b b' p
unify _ a b _ = error $ "Can't unify " ++ show a ++ " with " ++ show b
