module FRP.Core 
    ( Comonad(..)
    , Time
    , ExtEvent
    , Behavior(..)
    , Event(..)
    , untilB
    )
where

import qualified Graphics.UI.SDL as SDL

class (Functor w) => Comonad w where
    pull   :: w a -> a
    cojoin :: w a -> w (w a)
    (=>>)  :: w a -> (w a -> b) -> w b

    w =>> f  = fmap f (cojoin w)
    cojoin w = w =>> id

type Time = Double
type ExtEvent = SDL.Event

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

data Event :: * -> * where
    EVNever    :: Event a
    EVConst    :: Time -> a -> Event a
    EVExt      :: (ExtEvent -> Maybe (Event a)) -> Event a
    EVPred     :: Behavior (Maybe (Time,a)) -> Event a
    EVChoice   :: Event a -> Event a -> Event a
    EVSnapshot :: Event a -> Behavior b -> Event (a,b)
    EVJoin     :: Event (Event a) -> Event a

infixl 2 +=>

(+=>) :: Event a -> (Time -> a -> b) -> Event b
EVNever        +=> _ = EVNever
EVConst t x    +=> f = EVConst t (f t x)
EVExt f'       +=> f = EVExt (fmap (+=> f) . f')
EVPred b       +=> f = EVPred (fmap (fmap (\(t,a) -> (t,f t a))) b)
EVChoice x y   +=> f = EVChoice (x +=> f) (y +=> f)
EVSnapshot e b +=> f = e +=> (\t x -> f t (x, pull b))
EVJoin e       +=> f = EVJoin (e +=> (\_ x -> x +=> f))

instance Functor Event where
    fmap f x = x +=> const f
    {-
    fmap _ EVNever = EVNever
    fmap f (EVConst t x) = EVConst t (f x)
    fmap f (EVExt f') = EVExt (\e -> fmap (fmap f) (f' e))
    fmap f (EVPred b) = EVPred (fmap (fmap f) b)
    fmap f (EVChoice x y) = EVChoice (fmap f x) (fmap f y)
    fmap f (EVSnapshot e b) = fmap (\x -> f (x, pull b)) e
    fmap f (EVJoin e) = EVJoin (fmap (fmap f) e)
    -}

untilB :: Behavior a -> Event (Behavior a) -> Behavior a
untilB b (EVNever) = b
untilB b (EVConst t a) = if bTime b < t then b else a
untilB b (EVExt f) = b { bTrans = maybe b (untilB b) . f }
untilB b (EVPred b') = maybe b snd (pull b')
untilB b (EVChoice x y) = untilB (untilB b y) x
-- EVSnapshot impossible: (a,b) /~ Behavior a
untilB b (EVJoin e) = untilB b (fmap (untilB b) e)
