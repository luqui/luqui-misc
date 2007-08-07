{-# OPTIONS_GHC -fglasgow-exts -fth #-}

module Accessor
    (Accessor, nameDeriveAccessors, deriveAccessors, getVal, setVal) 
where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe (catMaybes)
import Control.Monad (guard)

data Accessor s a
    = Accessor { getVal :: s -> a
               , setVal :: a -> s -> s
               }

-- must satisfy the following laws:
-- getVal a (setVal a x s) == x
-- setVal a (getVal a s) s == s

deriveAccessors :: Name -> Q [Dec]
deriveAccessors n = nameDeriveAccessors n transformName
    where
    transformName s = do
        guard $ not (null s)
        guard $ last s == '_'
        return $ init s

nameDeriveAccessors :: Name -> (String -> Maybe String) -> Q [Dec]
nameDeriveAccessors t namer = do
    TyConI (DataD _ name _ cons _) <- reify t
    (return . concat) =<< mapM makeAccs cons

    where

    makeAccs :: Con -> Q [Dec]
    makeAccs (RecC _ vars) = do
        mdecs <- mapM (\ (name,_,_) -> makeAccFromName name) vars
        return $ catMaybes mdecs
    makeAccs (ForallC _ _ c) = makeAccs c
    makeAccs _ = return []

    transformName :: Name -> Maybe Name
    transformName (Name occ f) = do
        n <- namer (occString occ)
        return $ Name (mkOccName n) f

    makeAccFromName :: Name -> Q (Maybe Dec)
    makeAccFromName name = do
        case transformName name of
            Nothing -> return Nothing
            Just n -> makeAcc name n >>= return . Just

    makeAcc :: Name -> Name -> Q Dec
    makeAcc name accName = do
        body <- [|
            Accessor { getVal = $( return $ VarE name )
                     , setVal = \x s ->
                        $( return $ RecUpdE (VarE 's) [(name, VarE 'x)] )
                     }
                |]
        return $ ValD (VarP accName) (NormalB body) []
