module Functionator.MockFunctions where

import Functionator.AST
import qualified Data.Map as Map


mockEnv :: Map.Map Var Type
mockEnv = Map.fromList
    [ "(+)"     .:: TVar "Int" --> TVar "Int" --> TVar "Int"
    , "(-)"     .:: TVar "Int" --> TVar "Int" --> TVar "Int"
    , "(*)"     .:: TVar "Int" --> TVar "Int" --> TVar "Int"
    , "0"       .:: TVar "Int"
    , "succ"    .:: TVar "Int" --> TVar "Int"
    , "pred"    .:: TVar "Int" --> TVar "Int"
    , "even"    .:: TVar "Int" --> TVar "Bool"
    , "odd"     .:: TVar "Int" --> TVar "Bool"
    , "if"      .:: TPi "a" (TVar "Bool" --> TVar "a" --> TVar "a" --> TVar "a")
    , "not"     .:: TVar "Bool" --> TVar "Bool"
    , "head"    .:: TPi "a" (TVar "[]" %% TVar "a" --> TVar "a")
    , "tail"    .:: TPi "a" (TVar "[]" %% TVar "a" --> TVar "[]" %% TVar "a")
    , "cons"    .:: TPi "a" (TVar "a" --> TVar "[]" %% TVar "a" --> TVar "[]" %% TVar "a")
    , "nil"     .:: TPi "a" (TVar "[]" %% TVar "a")
    , "map"     .:: TPi "a" (TPi "b" ((TVar "a" --> TVar "b") --> TVar "[]" %% TVar "a" --> TVar "[]" %% TVar "b"))
    , "fix"     .:: TPi "a" ((TVar "a" --> TVar "a") --> TVar "a")
    ]
    where
    infixr 8 -->
    t --> u = makeArrow t u
    infix 1 .::
    (.::) = (,)
    infixl 9 %%
    (%%) = TApp
