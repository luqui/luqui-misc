module FRP.Core 
    ( Comonad(..)
    , Time
    , ExtEvent
    , Behavior(..)
    , Event(..)
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
type ExtEvent = ()

data DriveEvent 
    = TimeStepEvent
    | ExtEvent ExtEvent

type Driver = (Time,DriveEvent)

data Behavior a
    = Behavior { bEval  :: a
               , bTrans :: (Driver -> Behavior a)
               }

instance Functor Behavior where
    fmap f (Behavior eval trans) = 
        Behavior { bEval  = f eval
                 , bTrans = fmap f . trans
                 }

instance Comonad Behavior where
    pull = bEval
    b =>> f =
        Behavior { bEval  = f b
                 , bTrans = \e -> bTrans b e =>> f
                 }

constB :: a -> Behavior a
constB x = let r = Behavior { bEval = x, bTrans = const r } in r

zipB :: Behavior a -> Behavior b -> Behavior (a,b)
zipB b b' = tup (b, b')
    where
    tup (t,t') = Behavior { bEval = (bEval t, bEval t')
                          , bTrans = \e -> tup (bTrans t e, bTrans t' e)
                          }

data Event :: * -> * where
    EVNever    :: Event a
    EVDriver   :: Behavior (Maybe a) -> Event a
    EVChoice   :: Event a -> Event a -> Event a
    EVSnapshot :: Event a -> Behavior b -> Event (a,b)
    EVJoin     :: Event (Event a) -> Event a

instance Functor Event where
    fmap _ EVNever          = EVNever
    fmap f (EVDriver b)     = EVDriver (fmap (fmap f) b)
    fmap f (EVChoice x y)   = EVChoice (fmap f x) (fmap f y)
    fmap f (EVSnapshot e b) = fmap (\x -> f (x, pull b)) e
    fmap f (EVJoin e)       = EVJoin (fmap (fmap f) e)

untilB :: Behavior a -> Event (Behavior a) -> Behavior a
untilB b (EVNever)      = b
untilB b (EVDriver b')  = 
    case pull b' of
         Nothing -> 
            Behavior { bEval  = pull b
                     , bTrans = \e -> untilB (bTrans b e) (EVDriver (bTrans b' e))
                     }
         Just x -> x
untilB b (EVChoice x y) = untilB (untilB b y) x
untilB b (EVJoin e)     = untilB b (fmap (untilB b) e)
-- EVSnapshot impossible, (a,b) /~ Behavior c

time :: Behavior Double
time = genB 0
    where
    genB t = Behavior { bEval = t
                      , bTrans = \(t',_) -> genB (t+t')
                      }

step :: Double -> Behavior a -> Behavior a
step size b = bTrans b (size,TimeStepEvent)

delay :: Double -> Behavior a -> Event a
delay offs b = EVDriver $ 
    zipB time b =>> \w -> 
        if fst (pull w) >= offs
           then Just (snd (pull w))
           else Nothing
