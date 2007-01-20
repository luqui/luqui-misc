{-# OPTIONS_GHC -fglasgow-exts #-}

module Val 
    ( Val(..)
    , Pad
    , Eval
    )
    where

import AST
import qualified Data.Map as Map
import Control.Monad.Reader

type Pad = Map.Map Var Val
type Eval a = ReaderT Pad IO a  -- just try to put this into Eval.hs
                                -- circular dependency time!

data Val where
    VLit   :: Lit               -> Val
    VFunc  :: Pad -> Var -> AST -> Val
    VMagic :: (Val -> Eval Val) -> Val

instance Show Val where
    show (VLit l)  = "VLit (" ++ show l ++ ")"
    show (VFunc p v ast) = "VFunc (" ++ show p ++ ") " ++ show v ++ " (" ++ show ast ++ ")"
    show (VMagic _) = "VMagic ..."

