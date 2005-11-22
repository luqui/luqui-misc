{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Eval where

import Control.Monad.Reader
import qualified Data.Map as Map

import Typist.AST

type Pad = Map.Map VarName Val

data Val
    = VLambda { vlamParam :: VarName, vlamBody :: AST, vlamPad :: Pad }

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
    arg <- eval (appFun app)
    with (Map.insert (vlamParam fun) arg (vlamPad fun)) $
        eval (vlamBody fun)

eval var@(Var {}) = do
    pad <- ask
    return $ pad Map.! varName var
