{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns -farrows #-}

module FRP.ArrowCore 
    ( Time
    , SF, (:>)
    , integral
    , integralD
    , time
    , holdSignal
    , constSF
    , mousePos
    , keyDown
    , runFRP
    , isJust
    , mouseButtonDown
    , joinSF
    , edgeToPulse
    , foldPulse
    )
where

import qualified FRP.Draw as Draw
import qualified FRP.Vector as Vec
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.Rendering.OpenGL as GL
import Control.Arrow
import Data.List (foldl')
import Control.Monad (when)
import Data.Maybe (isJust)

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


-- Accepts pulse events containing signals; aggregates into a list of 
-- signals, newest first (for no good reason).
joinSF :: SF (Maybe (SF () a)) [a]
joinSF = self []
    where
    self as = SF $ \msua ->
        let arrows = maybe id (:) msua $ as
            runs = map (\a -> runSF a ()) arrows
        in
            (map fst runs, \dri -> self (map (($ dri) . snd) runs))

integral :: (Vec.Vector v, Fractional (Vec.Field v)) => SF v v
integral = integral' Vec.zero
    where
    integral' q = SF $ \x ->
        (q, \d -> case d of
                       TimeStepEvent dt -> integral' (q Vec.^+^ fromDouble dt Vec.*^ x)
                       _                -> integral' q)
    fromDouble = fromRational . toRational

integralD :: SF Double Double
integralD = Vec.Scalar ^>> integral >>^ Vec.fromScalar

time :: SF () Double
time = constSF 1 >>> integralD

mousePos :: SF () (Double,Double)
mousePos = helper (0,0)
    where
    helper (x,y) = self
        where self = SF $ \() -> 
                ((x,y), \d -> case d of
                           ExtEvent (SDL.MouseMotion x' y' _ _) -> helper $ stupidTransform (x',y')
                           _                                    -> self)

stupidTransform (x,y) = (32 * fromIntegral x / 640 - 16, 12 - 24 * fromIntegral y / 480)

foldPulse :: (a -> b -> b) -> b -> SF (Maybe a) b
foldPulse f b0 = SF $ \ma ->
    case ma of
         Nothing -> (b0, const (foldPulse f b0))
         Just x  -> let next = f x b0 in (b0, const (foldPulse f next))

-- for converting from edge to pulse events
edgeToPulse :: SF (Maybe a) (Maybe a)
edgeToPulse = downState
    where
    downState = SF $ \ma ->
        case ma of
             Nothing -> (Nothing, const downState)
             Just x  -> (Just x, const upState)
    upState = SF $ \ma ->
        case ma of
             Nothing -> (Nothing, const downState)
             Just x  -> (Nothing, const upState)

-- An edge event stating whether the mouse is down and where it last clicked
mouseButtonDown :: SDL.MouseButton -> SF () (Maybe (Double,Double))
mouseButtonDown but = downState
    where
    downState = SF $ \() ->
        (Nothing, \ev -> case ev of
                              ExtEvent (SDL.MouseButtonDown x y but') ->
                                if but == but'
                                   then upState (stupidTransform (x,y))
                                   else downState
                              _ -> downState)
    upState pos = SF $ \() -> 
        (Just pos, \ev -> case ev of
                               ExtEvent (SDL.MouseButtonUp x y but') ->
                                 if but == but'
                                    then downState
                                    else upState pos
                               _ -> downState)

-- An edge event stating whether a particular key is down
keyDown :: SDL.SDLKey -> SF () (Maybe ())
keyDown ch = downState
    where
    downState = SF $ \() ->
        (Nothing, \ev -> case ev of
                              ExtEvent (SDL.KeyDown sym) -> 
                                if SDL.symKey sym == ch 
                                   then upState
                                   else downState
                              _ -> downState)
    upState = SF $ \() ->
        (Just (), \ev -> case ev of
                              ExtEvent (SDL.KeyUp sym) ->
                                if SDL.symKey sym == ch
                                   then downState
                                   else upState
                              _ -> upState)

holdSignal :: SF (Maybe a) (Maybe a)
holdSignal = SF $ \ev ->
    case ev of
         Nothing -> (Nothing, const holdSignal)
         Just x  -> (Just x, const $ constSF $ Just x)


constSF :: a -> SF b a
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
    timeStep = 0.02
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
