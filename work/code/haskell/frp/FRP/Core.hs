{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}

module FRP.Core 
    ( Comonad(..)
    , Time
    , ExtEvent
    , Behavior(..)
    , Event(..)
    , integral
    , zipB
    , withB, withB2, withB3
    , constB
    , untilB
    , time
    , delay
    , mousePos
    , runFRP
    )
where

import FRP.Comonad
import FRP.Draw as Draw
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.Rendering.OpenGL as GL
import Data.List (foldl')
import Control.Monad (when)
import Debug.Trace

type Time = Double
type ExtEvent = SDL.Event

data DriveEvent 
    = TimeStepEvent Time
    | ExtEvent ExtEvent

type Driver = DriveEvent

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

withB :: Behavior a -> (a -> b) -> Behavior b
withB = flip fmap

withB2 :: Behavior a -> Behavior b -> (a -> b -> c) -> Behavior c
withB2 a b f = fmap (uncurry f) $ zipB a b

withB3 :: Behavior a -> Behavior b -> Behavior c -> (a -> b -> c -> d) -> Behavior d
withB3 a b c f = fmap (uncurry (uncurry f)) $ zipB (zipB a b) c

integral :: Behavior Double -> Behavior Double
integral b = int 0 b
    where
    int s b =
        Behavior { bEval = s
                 , bTrans = \e -> 
                        case e of
                           TimeStepEvent dt -> 
                               let nextVal = s + dt * pull b
                               in int nextVal (bTrans b e)
                           _ -> int s (bTrans b e)
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
time = integral (constB 1)

step :: Double -> Behavior a -> Behavior a
step size b = bTrans b (TimeStepEvent size)

stepEvent :: ExtEvent -> Behavior a -> Behavior a
stepEvent ev b = bTrans b (ExtEvent ev)

delay :: Double -> Behavior a -> Event a
delay offs b = EVDriver $ 
    zipB time b =>> \w -> 
        if fst (pull w) >= offs
           then Just (snd (pull w))
           else Nothing


mousePos :: Behavior (Double,Double)
mousePos = genB (0,0)
    where
    genB (x,y) = let self = Behavior { bEval = (x,y)
                                     , bTrans = \e -> transFun e self
                                     }
                 in self
    transFun (ExtEvent (SDL.MouseMotion x' y' _ _)) _
        = genB ( 32 * fromIntegral x' / 640 - 16,
                -24 * fromIntegral y' / 480 + 12)
    transFun _ self
        = self


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
        putStrLn "-------------------"
        preTicks <- SDL.getTicks 
        events <- whileM (/= SDL.NoEvent) SDL.pollEvent
        let b' = foldl' (flip ($)) (step 0.05 b) (map stepEvent events)
        GL.clear [GL.ColorBuffer]
        Draw.runDraw (pull b')
        SDL.glSwapBuffers
        postTicks <- SDL.getTicks
        let timeTaken = fromIntegral (postTicks - preTicks) * 0.001
        when (timeTaken < 1) $ 
            SDL.delay (floor $ (1 - timeTaken) * 1000)
        when (not $ SDL.Quit `elem` events) $ do
            mainLoop b'

    whileM p m = do
        r <- m
        if p r
           then fmap (r:) $ whileM p m
           else return []



