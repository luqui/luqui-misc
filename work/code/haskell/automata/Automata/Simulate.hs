{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Simulate where

-- These are supposed to be the "big" abstractions of the 
-- program.  Unfortunately, they don't match the abstractions
-- in the paper at all.  This was a causality issue. :-)

-- Represents a cellular topology as described in the paper.
-- XXX - Except it doesn't, because I didn't know how I was
-- going to define it when I wrote this program.
class Topology c where
    update :: ([a] -> a) -> c a -> c a

-- Allows the program to retrieve all the states at a
-- particular moment in time.
class Configuration c where
    cells :: c a -> [a]
