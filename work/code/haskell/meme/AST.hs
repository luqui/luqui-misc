{-# OPTIONS_GHC -fglasgow-exts #-}

module AST 
    ( Var
    , AST(..)
    , Lit(..)
    , Builtin(..)
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
    Builtin :: Builtin   -> AST  
    -- extensions
    Type  :: Type -> AST -> AST
    Hole  ::                AST
    deriving Show

data Lit where
    LInt   :: Integer -> Lit
    LFloat :: Double  -> Lit
    LStr   :: String  -> Lit
    LBool  :: Bool    -> Lit
    deriving Show

-- we have builtins so that they can be polymorphically typed
data Builtin where
    BTuple :: [AST]        -> Builtin
    BTag   :: Tag -> AST   -> Builtin
    BIf    :: AST -> AST -> AST -> Builtin
    deriving Show
