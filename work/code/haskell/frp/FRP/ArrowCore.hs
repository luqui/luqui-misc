{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

module FRP.ArrowCore where

import qualified FRP.Draw as Draw
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.Rendering.OpenGL as GL
import Control.Arrow
import Data.List (foldl')
import Control.Monad (when)

type Time = Double
type ExtEvent = SDL.Event

data DriveEvent
    = TimeStepEvent Time
    | ExtEvent ExtEvent

type Driver = DriveEvent

newtype SF a b =
    SF { runSF :: a -> (b, Driver -> SF a b) }

type (:>) = SF

instance Arrow SF where
    arr f = let r = SF $ \a -> (f a, const r) in r
    first (SF f)  = SF $ \(b,d) -> 
        let (c,trans) = f b in ((c,d), first . trans)
    SF f >>> SF g = SF $ \b ->
        let (c,trans)  = f b
            (d,trans') = g c
        in (d, \dri -> trans dri >>> trans' dri)

instance ArrowLoop SF where
    loop (SF f) = SF $ \b ->
        let ((c,d), trans) = f (b,d) in (c, loop . trans)

instance ArrowChoice SF where
    left (SF f) = r
        where
        r = SF $ \bord ->
                    case bord of
                        Left b  -> let (c,trans) = f b in (Left c, left . trans)
                        Right d -> (Right d, const r)

integral :: Double -> SF Double Double
integral q = SF $ \x ->
    (q, \d -> case d of
                   TimeStepEvent dt -> integral (q + x*dt)
                   _                -> integral q)


time :: SF () Double
time = constSF 1 >>> integral 0

constSF :: a -> SF () a
constSF x = arr (const x)

stepDriver :: Driver -> SF () b -> SF () b
stepDriver dri (SF f) = snd (f ()) dri

stepTime :: Double -> SF () b -> SF () b
stepTime size = stepDriver (TimeStepEvent size)

stepExtEvent :: ExtEvent -> SF () b -> SF () b
stepExtEvent ext = stepDriver (ExtEvent ext)

runFRP :: SF () (Draw.Draw ()) -> IO ()
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
    timeStep = 0.05
    mainLoop b = do
        preTicks <- SDL.getTicks

        events <- whileM (/= SDL.NoEvent) SDL.pollEvent
        let b' = foldl' (flip ($)) b (map stepExtEvent events)
        
        GL.clear [GL.ColorBuffer]
        Draw.runDraw (fst (runSF b' ()))
        SDL.glSwapBuffers
        
        postTicks <- SDL.getTicks
        let timeTaken = fromIntegral (postTicks - preTicks) * 0.001
        when (timeTaken < timeStep) $
            SDL.delay (floor $ (timeStep - timeTaken) * 1000)

        when (not $ SDL.Quit `elem` events) $ do
            mainLoop (stepTime timeStep b')

    whileM p m = do
        r <- m
        if p r
           then fmap (r:) $ whileM p m
           else return []
