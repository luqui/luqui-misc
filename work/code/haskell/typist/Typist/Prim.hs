module Typist.Prim (
    nativePad,
) where

import Typist.AST
import Typist.Eval
import Typist.Syntax
import qualified Data.Map as Map

makeNative1 :: (Cast a) => (a -> Val) -> Val
makeNative1 f =
    VNative {
        vnatFunc = \v -> cast v >>= return . f
    }

makeNative2 :: (Cast a, Cast b) => (a -> b -> Val) -> Val
makeNative2 f = 
    VNative {
        vnatFunc = \v -> cast v >>= return . makeNative1 . f
    }

makeNative3 :: (Cast a, Cast b, Cast c) => (a -> b -> c -> Val) -> Val
makeNative3 f =
    VNative {
        vnatFunc = \v -> cast v >>= return . makeNative2 . f
    }

native :: String -> Val
-- Fundamental operations on Int
native "plus"  = makeNative2 $ \x y -> VLit (Int (x + y))
native "neg"   = makeNative1 $ \x ->   VLit (Int (-x))
native "times" = makeNative2 $ \x y -> VLit (Int (x * y))
native "leq"   = makeNative2 $ \x y -> VLit (Bool ((x :: Integer) <= (y :: Integer)))
-- Fundamental operations on Bool
native "if"    = makeNative3 $ \cond true false ->
                                 if cond then true else false
native "True"  = VLit (Bool True)
native "False" = VLit (Bool False)

-- This belongs in the prelude (but "let" depends on it)
native "fix"   = evalPure . parseAST $ "\\f -> (\\x -> f (\\y -> x x y)) (\\x -> f (\\y -> x x y))"

native x       = error ("undefined function: " ++ x)

allNatives :: [String]
allNatives = words "plus neg times leq if True False fix"

nativePad :: Pad
nativePad = Map.fromList [ (x, native x) | x <- allNatives ]
