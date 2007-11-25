module FRP 
    ( Comonad
    , Time
    , Behavior
    , time
    , Event
    , untilB
    )
where

class (Functor w) => Comonad w where
    pull   :: w a -> a
    cojoin :: w a -> w (w a)
    (=>>)  :: w a -> (w a -> b) -> w b

    w =>> f  = fmap f (cojoin w)
    cojoin w = w =>> id

type Time = Double

data ExtEvent

data Behavior a
    = Behavior { bEval  :: a
               , bTrans :: (ExtEvent -> Behavior a)
               , bTime  :: Time
               }

instance Functor Behavior where
    fmap f (Behavior eval trans t) = 
        Behavior { bEval  = f eval
                 , bTrans = fmap f . trans
                 , bTime  = t
                 }

instance Comonad Behavior where
    pull = bEval
    b =>> f =
        Behavior { bEval  = f b
                 , bTrans = \e -> bTrans b e =>> f
                 , bTime  = bTime b
                 }

time :: Behavior () -> Time
time = bTime

data Event :: * -> * where
    EVNever    :: Event a
    EVConst    :: Time -> a -> Event a
    EVExt      :: (ExtEvent -> Maybe (Event a)) -> Event a
    EVPred     :: Behavior (Maybe a) -> Event a
    EVChoice   :: Event a -> Event a -> Event a
    EVSnapshot :: Event a -> Behavior b -> Event (a,b)
    EVJoin     :: Event (Event a) -> Event a

instance Functor Event where
    fmap _ EVNever = EVNever
    fmap f (EVConst t x) = EVConst t (f x)
    fmap f (EVExt f') = EVExt (\e -> fmap (fmap f) (f' e))
    fmap f (EVPred b) = EVPred (fmap (fmap f) b)
    fmap f (EVChoice x y) = EVChoice (fmap f x) (fmap f y)
    fmap f (EVSnapshot e b) = fmap (\x -> f (x, pull b)) e
    fmap f (EVJoin e) = EVJoin (fmap (fmap f) e)

untilB :: Behavior a -> Event (Behavior a) -> Behavior a
untilB b (EVNever) = b
untilB b (EVConst t a) = if bTime b < t then b else a
untilB b (EVExt f) = b { bTrans = maybe b (untilB b) . f }
untilB b (EVPred b') = maybe b id (pull b')
untilB b (EVChoice x y) = untilB (untilB b y) x
-- EVSnapshot impossible: (a,b) /~ Behavior a
untilB b (EVJoin e) = untilB b (fmap (untilB b) e)
