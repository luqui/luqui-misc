module Fregl.LinearSplit
    ( LinearSplit
    , newLinearSplit
    , readLinearSplit
    )
where

import Fregl.Splittable
import qualified Data.Supply as Supply

newtype LinearSplit a = LinearSplit (Supply.Supply [a])

newLinearSplit :: [a] -> IO (LinearSplit a)
newLinearSplit xs = do
    LinearSplit `fmap` Supply.newSupply xs tail

readLinearSplit :: LinearSplit a -> IO a
readLinearSplit (LinearSplit sup) = return . head $ Supply.supplyValue sup

instance Splittable (LinearSplit a) where
    split (LinearSplit s) = 
        let (a,b) = Supply.split2 s in (LinearSplit a, LinearSplit b)
