module Funlog.AST (
    Item(..),
    Class(..),
    Case(..),
) where

data Item
    = IInt Integer
    | IStr String
    | IList [Item]

data Class = Class
               { className  :: String
               , classCases :: [Case] 
               }

data Case  = Case
               { caseName   :: String
               , caseSubs   :: [Class]
               , caseFun    :: [Item -> Item] -> Item -> Item
               }



instance Eq Item where
    (IInt i)   == (IInt j)   = i == j
    (IStr s)   == (IStr t)   = s == t
    (IList xs) == (IList ys) = xs == ys
    _ == _                   = False

instance Show Item where
    show (IInt i) = show i
    show (IStr s) = show s
    show (IList is) = show is

instance Show Class where
    show (Class { className = n }) = n

instance Show Case where
    show (Case { caseName = n }) = n
