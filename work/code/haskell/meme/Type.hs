{-# OPTIONS_GHC -fglasgow-exts #-}

module Type
    ( Type(..)
    , typeSup
    , typeInf
    )
where

type Tag = String

data Type where
    TAtom  :: String          -> Type
    TArrow :: Type -> Type    -> Type
    TTuple :: [Type]          -> Type
    TUnion :: [(Tag,Type)]    -> Type
    TVar   :: Integer         -> Type  -- only for use inside reconstructor!
    deriving (Show,Eq,Ord)


unionInsert :: (Type -> Type -> Type) -> (Tag,Type) -> [(Tag,Type)] -> [(Tag,Type)]
unionInsert bound (newtag,newtyp) ((tag,typ):rest)
    | newtag == tag  =  
        case bound typ newtyp of
            TAtom "Bot" -> rest
            x           -> (tag, x) : rest
    | otherwise      =  (tag,typ) : unionInsert bound (newtag,newtyp) rest
unionInsert _ new [] = [new]


makeUnion :: [(Tag,Type)] -> Type
makeUnion [] = TAtom "Bot"
makeUnion xs = TUnion xs


typeInf :: Type -> Type -> Type
typeInf (TAtom "Top") x = x
typeInf (TAtom "Bot") x = TAtom "Bot"
typeInf x (TAtom "Top") = x
typeInf x (TAtom "Bot") = TAtom "Bot"
typeInf (TAtom a) (TAtom b)
    | a == b    = TAtom a
    | otherwise = TAtom "Bot"
typeInf (TArrow a b) (TArrow a' b')
    = TArrow (typeSup a a') (typeInf b b')
typeInf (TTuple as) (TTuple bs)
    | length as == length bs = TTuple $ zipWith typeInf as bs
    | otherwise = TAtom "Bot"
typeInf (TUnion as) (TUnion bs)
    = makeUnion $ foldr (unionInsert typeInf) as bs
typeInf _ _ = TAtom "Bot"


typeSup :: Type -> Type -> Type
typeSup (TAtom "Top") x = TAtom "Top"
typeSup (TAtom "Bot") x = x
typeSup x (TAtom "Top") = TAtom "Top"
typeSup x (TAtom "Bot") = x
typeSup (TAtom a) (TAtom b)
    | a == b    = TAtom a
    | otherwise = TAtom "Top"
typeSup (TArrow a b) (TArrow a' b')
    = TArrow (typeInf a a') (typeSup b b')
typeSup (TTuple as) (TTuple bs)
    | length as == length bs = TTuple $ zipWith typeSup as bs
    | otherwise = TAtom "Top"
typeSup (TUnion as) (TUnion bs)
    = makeUnion $ foldr (unionInsert typeSup) as bs
typeSup _ _ = TAtom "Top"
