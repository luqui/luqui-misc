{-# OPTIONS_GHC -fglasgow-exts #-}

module AST 
    ( Var
    , AST(..)
    , Lit(..)
    )
where

import Type

type Var = String

data AST where
    -- essential lambda calculus
    App   :: AST -> AST  -> AST
    Lam   :: Var -> AST  -> AST
    Var   :: Var         -> AST
    -- literals
    Lit   :: Lit         -> AST
    -- extensions
    Type  :: Type -> AST -> AST
    Hole  ::                AST
    deriving Show

data Lit where
    LInt   :: Integer -> Lit
    LFloat :: Double  -> Lit
    LStr   :: String  -> Lit
    deriving Show
