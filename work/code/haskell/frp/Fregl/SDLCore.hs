{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.SDLCore 
    ( Ev
    , runGameSDL
    , keyState
    , mousePos
    ) 
where

import Data.Maybe
import Control.Monad
import Control.Applicative
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU
import qualified Graphics.UI.SDL as SDL
import qualified Graphics.UI.SDL.TTF as TTF
import qualified Fregl.Event
import Fregl.Event
import Fregl.Signal
import Fregl.Vector
import Fregl.LinearSplit
import Fregl.Core hiding (when)
import qualified Fregl.Drawing as Draw
import Data.List
import qualified Data.Set as Set
import Data.IORef
import System.IO.Unsafe
import Control.Concurrent

data EventSDL
    = TimestepEvent Double
    | MouseEvent MouseEvent Vec2
    | KeyDownEvent Keysym
    | KeyUpEvent Keysym

data MouseEvent
    = MouseButton MouseButton MouseState [GL.Name]
    | MouseMotion

type Ev = Fregl.Event.Event EventSDL

instance EventVal EventSDL where
    wait = waitEvent >> return ()
    waitTimestep = waitHelper $ \e -> do
        TimestepEvent dt <- return e  -- fail does Nothing for us...
        return dt
    waitMouseMotion = waitHelper $ \e -> do
        MouseEvent MouseMotion pos <- return e
        return pos
    waitClickPos b s = waitHelper $ \e -> do
        MouseEvent (MouseButton b' s' _) pos <- return e
        guard $ b == b' && s == s'
        return pos
    waitClickName b s n = do
        e <- waitEvent
        case e of
            MouseEvent (MouseButton b' s' names) pos
                | b == b' && s == s' -> do
                    n' <- unsafeEventIO $ readLinearSplit $ Draw.getName n
                    if n' `elem` names then return pos else waitClickName b s n
            _ -> waitClickName b s n
    waitKeyDown = waitHelper $ \e -> do
        KeyDownEvent sym <- return e
        return sym
    waitKeyUp = waitHelper $ \e -> do
        KeyUpEvent sym <- return e
        return sym

waitHelper :: (EventSDL -> Maybe a) -> Ev a
waitHelper f = do
    e <- waitEvent
    case f e of
         Just x  -> return x
         Nothing -> waitHelper f

mousePosVar :: IORef (Double,Double)
mousePosVar = unsafePerformIO $ newIORef (0,0)

mousePos :: Signal (Double,Double)
mousePos = varSignal mousePosVar

keyStateVar :: IORef (Set.Set SDLKey)
keyStateVar = unsafePerformIO $ newIORef Set.empty

keyStateSig :: Signal (Set.Set SDLKey)
keyStateSig = varSignal keyStateVar

keyState :: SDLKey -> Signal Bool
keyState k = fmap (k `Set.member`) keyStateSig

runGameSDL :: (Draw.Name -> Ev (Signal Draw.Drawing)) -> IO ()
runGameSDL beh = do
    -- set up SDL
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 0 [SDL.OpenGL]

    -- set up OpenGL
    GL.texture GL.Texture2D GL.$= GL.Enabled
    GL.blend GL.$= GL.Enabled
    GL.blendFunc GL.$= (GL.SrcAlpha, GL.OneMinusSrcAlpha)

    -- set up ttf
    TTF.init

    name <- Draw.makeName
    cxt <- newEventCxt (beh name)
    pretime <- SDL.getTicks
    mainLoop cxt pretime
    TTF.quit
    SDL.quit


mainLoop cxt pretime = do
    let drawing = readEventCxt cxt
    -- draw it
    GL.clear [GL.ColorBuffer]
    GL.matrixMode GL.$= GL.Projection
    GL.loadIdentity
    initGLMatrix
    GL.matrixMode GL.$= GL.Modelview 0
    Draw.runDrawing drawing
    SDL.glSwapBuffers

    errors <- GL.get GLU.errors
    unless (null errors) $
        fail $ "OpenGL errors: " ++ show errors
 
    -- poll for events
    events <- whileM (/= SDL.NoEvent) SDL.pollEvent

    when (not $ any isQuitEvent events) $ do
        events' <- catMaybes <$> mapM (convertEvent drawing) events
        cxt' <- foldM (\cx ev -> nextEventCxt ev cx) cxt events'
        posttime <- SDL.getTicks
        let delay :: Int = 1000 * (33 - (fromIntegral posttime - fromIntegral pretime))
        when (delay > 0) $
            threadDelay (fromIntegral delay)
        posttime' <- SDL.getTicks
        let timediff = fromIntegral (posttime' - pretime) / 1000
        cxt'' <- nextEventCxt (TimestepEvent timediff) cxt'
        mainLoop cxt'' posttime'

convertEvent _ (SDL.MouseMotion x y _ _) = do
    let pos = convertCoords x y
    writeIORef mousePosVar pos
    return $ Just $ MouseEvent MouseMotion pos
convertEvent d (SDL.MouseButtonDown x y but) = do
    hits <- getHits d (fromIntegral x) (fromIntegral y)
    let but' = case but of
         SDL.ButtonLeft  -> Just ButtonLeft
         SDL.ButtonRight -> Just ButtonRight
         _               -> Nothing
    return $ fmap (\b -> 
                MouseEvent (MouseButton b MouseDown hits) (convertCoords x y)
             ) but'
convertEvent d (SDL.MouseButtonUp x y but) = do
    hits <- getHits d (fromIntegral x) (fromIntegral y)
    let but' = case but of
         SDL.ButtonLeft  -> Just ButtonLeft
         SDL.ButtonRight -> Just ButtonRight
         _               -> Nothing
    return $ fmap (\b -> 
                MouseEvent (MouseButton b MouseUp hits) (convertCoords x y)
             ) but'
convertEvent d (SDL.KeyDown sym) = do
    do  s <- readIORef keyStateVar
        writeIORef keyStateVar $! Set.insert (symKey sym) s
    return $ Just $ KeyDownEvent sym
convertEvent d (SDL.KeyUp   sym) = do
    do  s <- readIORef keyStateVar
        writeIORef keyStateVar $! Set.delete (symKey sym) s
    return $ Just $ KeyUpEvent sym
convertEvent _ _ = return $ Nothing

getHits drawing x y = do
    ((), recs) <- GL.getHitRecords 64 $ do
        viewport <- GL.get GL.viewport
        GL.matrixMode GL.$= GL.Projection
        GL.loadIdentity
        GLU.pickMatrix (x,480-y) (1,1) viewport
        initGLMatrix
        GL.matrixMode GL.$= GL.Modelview 0
        Draw.runDrawing drawing
    return $ case recs of
        Nothing -> []
        Just hits -> nub $ concatMap (\(GL.HitRecord _ _ ns) -> ns) hits

convertCoords x y = ( 32 * fromIntegral x / 640 - 16
                    , 24 * (1 - fromIntegral y / 480) - 12
                    )

initGLMatrix = do
    mode' <- GL.get GL.matrixMode
    GL.matrixMode GL.$= GL.Projection
    GLU.ortho2D (-16) 16 (-12) 12
    GL.matrixMode GL.$= mode'

isQuitEvent SDL.Quit = True
isQuitEvent (SDL.KeyDown (SDL.Keysym { SDL.symKey = SDL.SDLK_ESCAPE })) = True
isQuitEvent _ = False

whileM :: (a -> Bool) -> IO a -> IO [a]
whileM cond action = do
    v <- action
    if cond v
       then fmap (v:) $ whileM cond action
       else return []
