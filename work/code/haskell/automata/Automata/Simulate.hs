{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Simulate where

class Topology c where
    update :: ([a] -> a) -> c a -> c a
