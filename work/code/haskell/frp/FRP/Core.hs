module FRP.Core 
    ( Comonad(..)
    , Time
    , ExtEvent
    , Behavior(..)
    , Event(..)
    , zipB
    , constB
    , untilB
    , time
    , delay
    , runFRP
    )
where

import FRP.Draw as Draw
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.Rendering.OpenGL as GL
import Data.List (foldl')
import Control.Monad (when)

class (Functor w) => Comonad w where
    pull   :: w a -> a
    cojoin :: w a -> w (w a)
    (=>>)  :: w a -> (w a -> b) -> w b

    w =>> f  = fmap f (cojoin w)
    cojoin w = w =>> id

type Time = Double
type ExtEvent = SDL.Event

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
step size b = bTrans b (size, TimeStepEvent)

stepEvent :: Double -> ExtEvent -> Behavior a -> Behavior a
stepEvent size ev b = bTrans b (size, ExtEvent ev)

delay :: Double -> Behavior a -> Event a
delay offs b = EVDriver $ 
    zipB time b =>> \w -> 
        if fst (pull w) >= offs
           then Just (snd (pull w))
           else Nothing





runFRP :: Behavior (Draw.Draw ()) -> IO ()
runFRP b = do
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]
    GL.matrixMode GL.$= GL.Projection
    GL.loadIdentity
    GL.ortho2D (-16) 16 (-12) 12
    GL.matrixMode GL.$= GL.Modelview 0
    GL.loadIdentity
    mainLoop b
    SDL.quit

    where
    mainLoop b = do
        events <- whileM (/= SDL.NoEvent) SDL.pollEvent
        let b' = foldl' (flip ($)) (step 0.05 b) (map (stepEvent 0) events)
        GL.clear [GL.ColorBuffer]
        Draw.runDraw (pull b')
        SDL.glSwapBuffers
        when (not $ SDL.Quit `elem` events) $ do
            mainLoop b'

    whileM p m = do
        r <- m
        if p r
           then fmap (r:) $ whileM p m
           else return []



