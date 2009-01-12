module HeteroMap 
    ( (:>>), then_refl, then_trans
    , Ref, HeteroMap
    , empty, newRef, readRef, writeRef
    )
where

import Data.Unique
import GHC.Prim (Any)
import qualified Data.Map as Map
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)

data s :>> s' = FakeThen

then_refl :: s :>> s
then_refl = FakeThen

then_trans :: s :>> s' -> s' :>> s'' -> s :>> s''
then_trans FakeThen FakeThen = FakeThen

newtype Ref s a = Ref Unique
newtype HeteroMap s = HeteroMap (Map.Map Unique Any)

empty :: (forall s. HeteroMap s -> b) -> b
empty cc = cc (HeteroMap Map.empty)

newRef :: a -> HeteroMap s -> (forall s'. s :>> s' -> (Ref s' a, HeteroMap s') -> b) -> b
newRef x0 (HeteroMap m) cc = cc FakeThen (Ref refid, HeteroMap (Map.insert refid (unsafeCoerce x0) m))
    where
    {-# NOINLINE refid #-}
    refid = unsafePerformIO newUnique

readRef :: s :>> s' -> Ref s a -> HeteroMap s' -> a
readRef FakeThen (Ref refid) (HeteroMap m) = unsafeCoerce (fromJust $ Map.lookup refid m)

writeRef :: s :>> s' -> Ref s a -> a -> HeteroMap s' -> HeteroMap s'
writeRef FakeThen (Ref refid) x (HeteroMap m) = HeteroMap (Map.insert refid (unsafeCoerce x) m)
