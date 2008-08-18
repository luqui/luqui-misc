module Event where

import Stream
import Control.Arrow (second)
import Data.Monoid
import Control.Monad

type DTime = Double

newtype EventF i o = EventF { runEventF :: StreamF (DTime,i) (DTime,o) }

instance Functor (EventF i) where
    fmap f (EventF sf) = EventF (fmap (second f) sf)

adjust' :: DTime -> StreamF (DTime,i) (DTime,o) -> StreamF (DTime,i) (DTime,o)
adjust' dt (Read f)           = Read (adjust' dt . f)
adjust' dt (Write (dt',x) sf) = Write (dt'-dt,x) sf

adjust :: DTime -> EventF i o -> EventF i o
adjust dt (EventF e) = EventF (adjust' dt e)

idE :: EventF i i
idE = EventF (Read (\i -> Write i (runEventF idE)))

merge :: EventF i o -> EventF i o -> EventF i o
merge (EventF a) (EventF b) = EventF $ go a b
    where
    -- ow my eyes
    go sfa@(Write (dta,a) resta) sfb@(Write (dtb,b) restb)
        | dta <= dtb = Write (dta,a) (go resta (adjust' dta sfb))
        | otherwise  = Write (dtb,b) (go (adjust' dtb sfa) restb)
    go sfa@(Read {}) (Write (dtb,b) restb) =
        Write (dtb,b) (go (adjust' dtb sfa) restb)
    go (Write (dta,a) resta) sfb@(Read {}) =
        Write (dta,a) (go resta (adjust' dta sfb))
    go (Read ia) (Read ib) =
        Read $ \r -> go (ia r) (ib r)

instance Monoid (EventF i o) where
    mempty = let e = Read (const e) in EventF e
    mappend = merge

instance Monad (EventF i) where
    return x = EventF $ Write (0,x) (runEventF mempty)
    EventF (Read ia) >>= f = 
        EventF (Read (\i -> runEventF (EventF (ia i) >>= f)))
    EventF (Write (dt,x) sf) >>= f = 
        merge (adjust (-dt) (f x)) (EventF sf >>= f)
