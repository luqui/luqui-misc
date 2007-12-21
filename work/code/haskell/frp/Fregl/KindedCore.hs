module KindedCore where

import Fregl.FMonad
import Control.Arrow hiding (pure)
import Control.Applicative
import Debug.Trace

type Time = Double

-- contravariant time = the timestep to the next value I want
-- covariant time = if not Nothing, then a smaller time 
-- representing the actual step
--       (will be no greater than contravariant time)
-- Yaay it's been newtyped, so we can in the future add
-- a transition "tag" representing how likely it is to
-- pitch a fit, and execute the more likely one first.
newtype Transition a 
    = Transition { runTransition :: Time -> FMonad (a, Maybe Time) }

mapTrans :: (a -> b) -> Transition a -> Transition b
mapTrans f t = Transition $ fmap (first f) . runTransition t

constTrans :: a -> Transition a
constTrans x = Transition $ const $ return (x, Nothing)

-- finds the greatest dt that both transitions will accept, and extracts
-- their values
negotiateTrans :: Transition a -> Transition b -> Transition (a,b)
negotiateTrans ta tb = Transition $ \dt -> do
    transa <- runTransition ta dt
    case transa of
         (a, Nothing)  -> runTransition (half Nothing a ta tb) dt
         (a, Just dt') -> runTransition (half (Just dt') a ta tb) dt'
    where
    half :: Maybe Time -> a -> Transition a -> Transition b -> Transition (a,b)
    half def cura ta tb = Transition $ \dt -> do
        transb <- runTransition tb dt
        case transb of
             (b, Nothing)  -> return ((cura,b), def)
             (b, Just dt') -> 
                runTransition (mapTrans flipPair (half (Just dt') b tb ta)) dt'
    flipPair (x,y) = (y,x)

negotiateTransWith :: (a -> b -> c) -> Transition a -> Transition b -> Transition c
negotiateTransWith f ta tb = mapTrans (uncurry f) $ negotiateTrans ta tb
        

requestDT :: Time -> Time -> Maybe Time
requestDT req dt
    | req < dt  = Just req
    | otherwise = Nothing

-- SF - Signal functions, work on continuous Streams and
--      discrete Events alike

newtype SF b c 
    = SF { runSF :: Transition (b -> (c, SF b c)) }

instance Arrow SF where
    arr f = SF $ constTrans (\b -> (f b, arr f))

    SF f >>> SF g = SF $ negotiateTransWith compose f g
        where
        compose f g b =
            let (c, f') = f b
                (d, g') = g c
            in (d, f' >>> g')

    first (SF f) = SF $ mapTrans first' f
        where
        first' f (b,d) =
            let (c, f') = f b
            in ((c,d), first f')

instance ArrowLoop SF where
    loop (SF f) = SF $ mapTrans loop' f
        where
        loop' f b =
            let ((c,d), f') = f (b,d)
            in (c, loop f')


-- Stream - continuous, demand-driven (reactive) signal

newtype Stream a = Stream (Transition (a, Stream a))

instance Functor Stream where
    fmap f (Stream trans) = Stream (mapTrans (f *** fmap f) trans)

instance Applicative Stream where 
    pure x = Stream $ 
        constTrans (x, pure x)
    Stream f <*> Stream x = Stream $ 
        negotiateTransWith (\(f,fs) (a,as) -> (f a, fs <*> as)) f x


applyStream :: SF b c -> Stream b -> Stream c
applyStream (SF sf) (Stream b) = Stream $ negotiateTransWith app sf b
    where
    app sf (b, b') = 
        let (c, sf') = sf b
        in (c, applyStream sf' b')


-- ack, decouple from Transition somehow
magicListToStream :: Time -> MagicList (Time,a) -> Stream (Maybe a)
magicListToStream time list = Stream $ Transition $ \dt -> do
    cons <- readMagicList list
    case cons of
         Just ((timestamp,hd),tl)
            | timestamp <= time -> -- ack, just get it out the door!
                return ((Just hd, magicListToStream time tl), requestDT 0 dt)
            | timestamp <= time + dt -> do
                let step = time + dt - timestamp
                return ((Just hd, magicListToStream (time+step) tl), requestDT step dt)
         _ ->
                return ((Nothing, magicListToStream (time+dt) list), Nothing)
