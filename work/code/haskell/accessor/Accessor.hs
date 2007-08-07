{-# OPTIONS_GHC -fglasgow-exts -fth #-}

module Accessor
    ( Accessor(..)
    , nameDeriveAccessors, deriveAccessors
    , getA, putA, modA
    , (.>), (<.), (=:)
    )
where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe (catMaybes)
import Control.Monad (guard)
import Control.Monad.State

data Accessor s a
    = Accessor { getVal :: s -> a
               , setVal :: a -> s -> s
               }

infixl 9 .> 
(.>) :: Accessor a b -> Accessor b c -> Accessor a c
f .> g = 
    Accessor { getVal = getVal g . getVal f
             , setVal = \c a -> setVal f (setVal g c (getVal f a)) a
             }

infixr 9 <.
(<.) :: Accessor b c -> Accessor a b -> Accessor a c
(<.) = flip (.>)

infix 1 =:
(=:) :: MonadState s m => Accessor s a -> a -> m ()
(=:) = putA

getA :: MonadState s m => Accessor s a -> m a
getA a = liftM (getVal a) get

putA :: MonadState s m => Accessor s a -> a -> m ()
putA a x = liftM (setVal a x) get >>= put

modA :: MonadState s m => Accessor s a -> (a -> a) -> m ()
modA a f = liftM f (getA a) >>= putA a

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
    liftM concat $ mapM makeAccs cons

    where

    makeAccs :: Con -> Q [Dec]
    makeAccs (RecC _ vars) =
        liftM catMaybes $ mapM (\ (name,_,_) -> makeAccFromName name) vars
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
            Just n -> liftM Just $ makeAcc name n

    makeAcc :: Name -> Name -> Q Dec
    makeAcc name accName = do
        body <- [|
            Accessor { getVal = $( return $ VarE name )
                     , setVal = \x s ->
                        $( return $ RecUpdE (VarE 's) [(name, VarE 'x)] )
                     }
                |]
        return $ ValD (VarP accName) (NormalB body) []
