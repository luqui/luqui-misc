{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Eval where

import Control.Monad.Reader
import qualified Data.Map as Map

import Typist.AST

type Pad = Map.Map VarName Val

data Val
    = VLambda { vlamParam :: VarName, vlamBody :: AST, vlamPad :: Pad }
    | VNative { vnatFunc :: Val -> Val }
    | VLit    { vlitVal :: ASTLit }

instance Show Val where
    show (VLambda { }) = "<lambda: ...>"
    show (VNative { }) = "<native: ...>"
    show (VLit (Int x)) = show x
    show (VLit (Bool x)) = show x

type Eval a = Reader Pad a

with :: MonadReader r m => r -> m a -> m a
with = local . const

eval :: AST -> Eval Val
eval lam@(Lambda {}) = do
    pad <- ask
    return $ VLambda {
                vlamParam = lamParam lam,
                vlamBody  = lamBody lam,
                vlamPad   = pad
             }

eval app@(App {}) = do
    fun <- eval (appFun app)
    arg <- eval (appArg app)
    case fun of
        VLambda {} -> 
            with (Map.insert (vlamParam fun) arg (vlamPad fun)) $
                eval (vlamBody fun)
        VNative {} ->
            return $ vnatFunc fun arg

eval var@(Var {}) = do
    pad <- ask
    return $ pad Map.! varName var

eval lit@(Lit {}) = return $ VLit (litLit lit)
