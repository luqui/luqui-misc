{-# OPTIONS_GHC -fglasgow-exts #-}

module Typist.Eval (
    Pad,
    Val(..),
    Eval, eval,
    Cast, cast
) where

import Control.Monad.Reader
import qualified Data.Map as Map
import Typist.AST

type Pad = Map.Map VarName Val

data Val
    = VLambda { vlamParam :: VarName, vlamBody :: AST, vlamPad :: Pad }
    | VNative { vnatFunc :: Val -> Eval Val }
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
            vnatFunc fun arg

eval var@(Var {}) = do
    pad <- ask
    return $ pad Map.! varName var

eval lit@(Lit {}) = return $ VLit (litLit lit)

class Cast a where
    cast :: Val -> Eval a

instance Cast Val where
    cast = return . id

instance (Cast a) => Cast (Val -> Eval a) where
    cast fun@(VLambda {}) = return $ \arg -> 
        with (Map.insert (vlamParam fun) arg (vlamPad fun)) $
            cast =<< eval (vlamBody fun)
            
    cast fun@(VNative {}) = return $ (\v -> cast =<< vnatFunc fun v)

instance Cast Integer where
    cast = return . intVal . vlitVal

instance Cast Bool where
    cast = return . boolVal . vlitVal
