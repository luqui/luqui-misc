module Functionator.Pretty where

import Text.PrettyPrint
import Functionator.AST

data ExpParenFlag
    = ExpParenFlag { parenApp :: Bool
                   , parenLam :: Bool
                   }

data TypeParenFlag
    = TypeParenFlag { parenArrow :: Bool
                    , parenTApp  :: Bool
                    }

formatExp :: Exp -> Doc
formatExp = prettyExp (ExpParenFlag False False)

formatType :: Type -> Doc
formatType = prettyType (TypeParenFlag False False)

par :: Bool -> Doc -> Doc
par True  = parens
par False = id

prettyExp :: ExpParenFlag -> Exp -> Doc
prettyExp pf (EVar v) = text v
prettyExp pf (ELambda v (TFree _) e) = par (parenLam pf) $
    char '\\' <> text v <> char '.' 
       <+> prettyExp (ExpParenFlag False False) e
prettyExp pf (ELambda v t e) = par (parenLam pf) $
    char '\\' <> text v <> char ':' <> prettyType (TypeParenFlag False False) t <> char '.' 
       <+> prettyExp (ExpParenFlag False False) e
prettyExp pf (EApp a b) = par (parenApp pf) $
    prettyExp (ExpParenFlag False True) a <+> prettyExp (ExpParenFlag True True) b
prettyExp pf (EType t e) = parens $
    prettyExp (ExpParenFlag False True) e <+> text ":" <+> prettyType (TypeParenFlag False False) t
prettyExp pf EHole = text "[__]"

prettyType :: TypeParenFlag -> Type -> Doc
prettyType pf (TVar v)  = text v
prettyType pf (TFree i) = text $ "^" ++ show i
prettyType pf (TPi v t) = par (parenArrow pf) $
    text "\\/" <> text v <> char '.' <+> prettyType (TypeParenFlag False False) t
prettyType pf (TApp (TApp (TVar "->") a) b) = par (parenArrow pf) $ 
    prettyType (TypeParenFlag True False) a <+> text "->"
        <+> prettyType (TypeParenFlag False False) b
prettyType pf (TApp a b) = par (parenTApp pf) $
    prettyType (TypeParenFlag True False) a <+> prettyType (TypeParenFlag True True) b
