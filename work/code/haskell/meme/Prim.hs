{-# OPTIONS_GHC -fglasgow-exts #-}

module Prim 
    ( builtins
    , builtinPad
    )
    where

import AST
import Val
import qualified Data.Map as Map
import Control.Monad.Reader

op1 :: (Val -> Eval Val) -> Val
op1 = VMagic

op2 :: (Val -> Val -> Eval Val) -> Val
op2 f = VMagic $ \x -> return . VMagic $ \y -> f x y

unitVal :: Val
unitVal = VTuple []

op1Show :: Val -> Eval Val
op1Show (VLit (LInt x))   = return . VLit . LStr $ show x
op1Show (VLit (LFloat x)) = return . VLit . LStr $ show x
op1Show (VLit (LStr x))   = return . VLit . LStr $ show x
op1Show (VFunc {})        = return . VLit . LStr $ "*func*"
op1Show (VMagic {})       = return . VLit . LStr $ "*func*"

op1Print :: Val -> Eval Val
op1Print (VLit (LStr str)) = do
    liftIO $ putStr str
    return unitVal

op1Say :: Val -> Eval Val
op1Say v = do
    op1Print v
    liftIO $ putStrLn ""
    return unitVal

-- Name, type, impl
builtins :: [(Var, Type, Val)]
builtins = [ ("print", TArrow (TAtom "Str") (TTuple []),   op1 op1Print)
           , ("say",   TArrow (TAtom "Str") (TTuple []),   op1 op1Say)
           , ("show",  TArrow (TAtom "Top") (TAtom "Str"), op1 op1Show)
           ]

builtinPad :: Pad
builtinPad = Map.fromList builtins
