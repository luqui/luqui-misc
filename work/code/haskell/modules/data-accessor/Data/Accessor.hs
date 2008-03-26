{-# OPTIONS_GHC -fglasgow-exts -fth #-}

-- |This module provides a simple abstract data type for
-- a "piece" of a data stucture that can be read from and
-- written to.  It provides an automatic Template Haskell
-- routine to scour data type definitions and generate
-- accessor objects for them automatically.

module Data.Accessor
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

-- |An @Accessor s a@ is an object that encodes how to
-- get and put a subject of type @a@ out of/into an object
-- of type @s@.
-- 
-- In order for an instance of this data structure @a@ to be
-- an "Accessor", it must obey the following laws:
-- 
-- > getVal a (setVal a x s) = x
-- > setVal a (getVal a s) s = s
data Accessor s a
    = Accessor { getVal :: s -> a
               , setVal :: a -> s -> s
               }

infixl 9 .> 
-- |Accessor composition.
(.>) :: Accessor a b -> Accessor b c -> Accessor a c
f .> g = 
    Accessor { getVal = getVal g . getVal f
             , setVal = \c a -> setVal f (setVal g c (getVal f a)) a
             }

infixr 9 <.
-- |Accessor composition the other direction. 
-- 
-- > (<.) = flip (.>)
(<.) :: Accessor b c -> Accessor a b -> Accessor a c
(<.) = flip (.>)

infix 1 =:
-- |An "assignment operator" for state monads.  
--
-- > (=:) = putA
(=:) :: MonadState s m => Accessor s a -> a -> m ()
(=:) = putA

-- |A structural dereference function for state monads.
getA :: MonadState s m => Accessor s a -> m a
getA a = liftM (getVal a) get

-- |A structural assignment function for state monads.
putA :: MonadState s m => Accessor s a -> a -> m ()
putA a x = get >>= put . setVal a x

-- |A structural modification function for state monads.
modA :: MonadState s m => Accessor s a -> (a -> a) -> m ()
modA a f = liftM f (getA a) >>= putA a

-- |@deriveAccessors n@ where @n@ is the name of a data type
-- declared with @data@ looks through all the declared fields
-- of the data type, and for each field ending in an underscore
-- generates an accessor of the same name without the underscore.
--
-- It is @nameDeriveAccessors n f@ where @f@ satisfies 
-- > f (s ++ "_") = Just s
-- > f x          = Nothing   -- otherwise
--
-- For example, given the data type:
--
-- > data Score = Score { p1Score_ :: Int
--                      , p2Score_ :: Int
--                      , rounds   :: Int
--                      }
--
-- @deriveAccessors@ will generate the following objects:
--
-- > p1Score :: Accessor Score Int
-- > p1Score = Accessor p1Score_ (\x s -> s { p1Score_ = x })
-- > p2Score :: Accessor Score Int
-- > p2Score = Accessor p2Score_ (\x s -> s { p2Score_ = x })
deriveAccessors :: Name -> Q [Dec]
deriveAccessors n = nameDeriveAccessors n transformName
    where
    transformName s = do
        guard $ not (null s)
        guard $ last s == '_'
        return $ init s

-- |@nameDeriveAccessors n f@ where @n@ is the name of a data type
-- declared with @data@ and @f@ is a function from names of fields
-- in that data type to the name of the corresponding accessor. If
-- @f@ returns @Nothing@, then no accessor is generated for that
-- field.
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
