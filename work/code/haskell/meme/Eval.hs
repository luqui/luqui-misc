{-# OPTIONS_GHC -fglasgow-exts #-}

module Eval
    ( Pad
    , Eval
    , runEval
    , Val(..)
    , eval
    )
where

import AST
import Val
import Prim
import qualified Data.Map as Map
import Control.Monad.Reader

runEval :: Eval a -> IO a
runEval e = runReaderT e builtinPad

eval :: AST -> Eval Val
eval (App f arg) = do
    func <- eval f
    argval <- eval arg
    case func of
        VFunc pad var ast -> local (Map.insert var argval . const pad) $ eval ast
        VMagic fn         -> fn argval
eval (Lam var ast) = do
    pad <- ask
    return $ VFunc pad var ast
eval (Var var) = do
    Map.lookup var =<< ask

eval (Type _ ast) = eval ast
eval Hole         = fail "Failed to infer hole"
eval (Lit lit)    = return $ VLit lit
