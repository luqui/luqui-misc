{-# OPTIONS_GHC -fglasgow-exts -fth #-}

module CallByFuture (cbf, cbfProgram) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Applicative
import Control.Parallel
import Control.Monad
import Debug.Trace

instance Applicative Q where
    pure = return
    (<*>) = ap

parApp :: (a -> b) -> (a -> b)
parApp f x = x `par` f x

cbf :: Exp -> Q Exp
cbf e = do
    parAppExp <- [| parApp |]
    let ?parApp = parAppExp in return $ cv e

cbfProgram :: Q [Dec] -> Q [Dec]
cbfProgram q = do
    parAppExp <- [| parApp |]
    let ?parApp = parAppExp
    ret <- fmap (map cvDec) q
    trace (show (ppr ret)) $ return ()
    return ret

cv (AppE a b)       = AppE (AppE ?parApp (cv a)) (cv b)
cv (InfixE e op e') = InfixE (fmap cv e) op (fmap cv e')
cv (LamE ps e)      = LamE ps (cv e)
cv (TupE es)        = TupE (map cv es)
cv (CondE c t f)    = CondE (cv c) (cv t) (cv f)
cv (LetE ds e)      = LetE (map cvDec ds) (cv e)
cv (CaseE e ms)     = CaseE (cv e) (map cvMatch ms)
cv (DoE ss)         = DoE (map cvStmt ss)
cv (CompE ss)       = CompE (map cvStmt ss)
cv (ListE es)       = ListE (map cv es)
cv (SigE e t)       = SigE (cv e) t
cv other            = other

cvDec (FunD name cs) = FunD name (map cvClause cs)
cvDec (ValD pat body decs) = ValD pat (cvBody body) (map cvDec decs)
cvDec (ClassD cxt name ns fundeps decs) = ClassD cxt name ns fundeps (map cvDec decs)
cvDec (InstanceD cxt t decs) = InstanceD cxt t (map cvDec decs)
cvDec other = other

cvClause (Clause pats body decs) = Clause pats (cvBody body) (map cvDec decs)

cvMatch (Match pat body dec) = Match pat (cvBody body) (map cvDec dec)

cvStmt (BindS pat e) = BindS pat (cv e)
cvStmt (LetS decs) = LetS (map cvDec decs)
cvStmt (NoBindS e) = NoBindS (cv e)
cvStmt (ParS sss) = ParS (map (map cvStmt) sss)

cvBody (GuardedB ges) = GuardedB [ (g,cv e) | (g,e) <- ges ]
cvBody (NormalB e) = NormalB (cv e)
