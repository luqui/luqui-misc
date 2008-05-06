----------------------------------------------
-- |
-- Module    : Control.Monad.Omega
-- Copyright : (c) Luke Palmer 2008
-- License   : Public Domain
--
-- Maintainer : Luke Palmer <lrpalmer@gmail.com>
-- Stability : experimental
-- Portability : portable
--
-- A monad for enumerating sets: like the list monad, but
-- \"breadth-first\".
--
-- It addresses the problem seen when trying to generate
-- the list of all pairs of naturals with
-- @[ (x,y) | x <- [0..], y <- [0..] ]@, which is broken
-- since the first element of every reachable pair will
-- be 0.
--
-- Using Omega this can be written
-- 
-- > pairs = runOmega $ do
-- >     x <- each [0..]
-- >     y <- each [0..]
-- >     return (x,y)
--
-- More precisely, if @x@ appears at a finite index in
-- @xs@, and @y@ appears at a finite index in @f x@,
-- then @y@ will appear at a finite index in
-- @each xs >>= f@. 
----------------------------------------------

module Control.Monad.Omega 
    (diagonal, Omega, runOmega, each) 
where

import qualified Control.Monad as Monad
import qualified Control.Applicative as Applicative
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

-- | This is the hinge algorithm of the Omega monad,
-- exposed because it can be useful on its own.  Joins 
-- a list of lists with the property that for every x y 
-- there is an n such that @xs !! x !! y == diagonal xs !! n@.
diagonal :: [[a]] -> [a]
diagonal = concat . stripe
    where
    stripe [] = []
    stripe ([]:xss) = stripe xss
    stripe ((x:xs):xss) = [x] : zipCons xs (stripe xss)

    zipCons [] ys = ys
    zipCons xs [] = map (:[]) xs
    zipCons (x:xs) (y:ys) = (x:y) : zipCons xs ys

newtype Omega a = Omega { runOmega :: [a] }

each :: [a] -> Omega a
each = Omega

instance Functor Omega where
    fmap f (Omega xs) = Omega (map f xs)

instance Monad Omega where
    return x = Omega [x]
    Omega m >>= f = Omega $ diagonal $ map (runOmega . f) m
    fail _ = Omega []

instance Applicative.Applicative Omega where
    pure = return
    (<*>) = Monad.ap

instance Foldable.Foldable Omega where
    foldMap f (Omega xs) = Foldable.foldMap f xs

instance Traversable.Traversable Omega where
    traverse f (Omega xs) = fmap Omega $ Traversable.traverse f xs
