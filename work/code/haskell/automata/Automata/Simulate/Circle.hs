{-# OPTIONS_GHC -fglasgow-exts #-}

module Automata.Simulate.Circle where

import Automata.Simulate
import Data.Array
import Data.List

data Circle a =
    Circle {
        cells  :: Array Int a,
        size   :: Int,
        radius :: Int }

makeCircle :: Int -> [a] -> Circle a
makeCircle rad xs = Circle {
    cells  = listArray (0, length xs - 1) xs,
    size   = length xs,
    radius = rad }
    

neighbors :: Circle a -> Int -> [a]
neighbors circ pos = map ((cells circ !) . (`mod` size circ)) $
                         map (+ pos) [-radius circ..radius circ]

instance Topology Circle where
    update f circ = 
        circ { cells = listArray (0, size circ - 1) $ 
                         map (f . neighbors circ) (indices $ cells circ) }

instance (Show a) => Show (Circle a) where
    show circ = concat . intersperse " " . map show . elems . cells $ circ
