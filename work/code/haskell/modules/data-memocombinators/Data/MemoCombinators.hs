------------------------------------------------
-- |
-- Module    : Data.MemoCombinators
-- Copyright : (c) Luke Palmer 2008
-- License   : BSD3
--
-- Maintainer : Luke Palmer <lrpalmer@gmail.com>
-- Stability  : experimental
-- Portability : presumably portable
--
-- This module provides combinators for building memo tables
-- over various data types, so that the type of table can
-- be customized depending on the application.
------------------------------------------------

module Data.MemoCombinators 
    ( Memo
    , memo2, memo3, memoSecond, memoThird
    , bool
    , RangeMemo
    , arrayRange
    , chunks
    )
where

import qualified Data.Array as Array

-- | The type of a memo table.
type Memo a = forall r. (a -> r) -> (a -> r)

-- | Memoize a two argument function (just apply the table directly for
-- single argument functions).
memo2 :: Memo a -> Memo b -> (a -> b -> r) -> (a -> b -> r)
memo2 a b = a . (b .)

-- | Memoize a three argument function.
memo3 :: Memo a -> Memo b -> Memo c -> (a -> b -> c -> r) -> (a -> b -> c -> r)
memo3 a b c = a . (memo2 b c .)

-- | Memoize the second argument of a function.
memoSecond :: Memo b -> (a -> b -> r) -> (a -> b -> r)
memoSecond b = (b .)

-- | Memoize the third argument of a function.
memoThird :: Memo c -> (a -> b -> c -> r) -> (a -> b -> c -> r)
memoThird c = (memoSecond c .)

-- | A memo table for bools.
bool :: Memo Bool
bool f = cond (f True) (f False)
    where
    cond t f True  = t
    cond t f False = f

-- | The type of builders for ranged tables; takes a lower bound and an upper
-- bound, and returns a memo table for that range.  The table's behavior is
-- undefined for values outside that range.
type RangeMemo a = a -> a -> Memo a

-- | Build a memo table for a range using a flat array.
arrayRange :: (Array.Ix a) => RangeMemo a
arrayRange lo hi f = (Array.listArray rng (map f (Array.range rng)) Array.!)
    where rng = (lo,hi)

-- | Given a list of ranges, (lazily) build a memo table for each one
-- and combine them using linear search.
chunks :: (Array.Ix a) => RangeMemo a -> [(a,a)] -> Memo a
chunks rmemo cs f = lookup (cs `zip` map (\(a,b) -> rmemo a b f) cs)
    where
    lookup [] _ = error "Element non in table"
    lookup ((r,c):cs) x | Array.inRange r x = c x
                        | otherwise = lookup cs x
