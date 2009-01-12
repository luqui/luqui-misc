{-# LANGUAGE IncoherentInstances #-}

module HeteroMap 
    ( Ref, HeteroMap
    , empty, newRef, readRef, writeRef
    )
where

import Data.Unique
import GHC.Prim (Any)
import qualified Data.Map as Map
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)

class Then a b
instance Then () ()
instance Then xs ys => Then (x,xs) (y,ys)
instance Then xs ys => Then xs (y,ys)

newtype Ref s a = Ref Unique
newtype HeteroMap s = HeteroMap (Map.Map Unique Any)

empty :: HeteroMap ()
empty = HeteroMap Map.empty

newRef :: a -> HeteroMap s -> (forall s'. Ref (s',s) a -> HeteroMap (s',s) -> b) -> b
newRef x0 (HeteroMap m) cc = cc (Ref refid) (HeteroMap (Map.insert refid (unsafeCoerce x0) m))
    where
    {-# NOINLINE refid #-}
    refid = unsafePerformIO newUnique

readRef :: Then s s' => Ref s a -> HeteroMap s' -> a
readRef (Ref refid) (HeteroMap m) = unsafeCoerce (fromJust $ Map.lookup refid m)

writeRef :: Then s s' => Ref s a -> a -> HeteroMap s' -> HeteroMap s'
writeRef (Ref refid) x (HeteroMap m) = HeteroMap (Map.insert refid (unsafeCoerce x) m)
