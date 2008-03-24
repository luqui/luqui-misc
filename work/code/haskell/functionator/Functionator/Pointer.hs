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
