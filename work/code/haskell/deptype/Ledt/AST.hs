module Ledt.AST 
    ( AST(..)
    , ASTInfer(..) ) 
where

import Prelude hiding (pi)

infixl 0 %
class AST ast where
    lam  :: ast -> (ast -> ast) -> ast
    pi   :: ast -> (ast -> ast) -> ast
    (%)  :: ast -> ast -> ast
    set  :: Integer -> ast

class (AST ast) => ASTInfer ast where
    lam_ :: (ast -> ast) -> ast
    pi_  :: (ast -> ast) -> ast
