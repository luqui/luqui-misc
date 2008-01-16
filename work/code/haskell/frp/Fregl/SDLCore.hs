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
import Fregl.EventVal
import Fregl.WFQueue
import Fregl.Core hiding (when)
import qualified Fregl.Drawing as Draw
import Data.List
import qualified Data.Set as Set
import Control.Concurrent.STM
import System.IO.Unsafe
import Control.Concurrent

type Ev = Fregl.Event.Event

mousePosVar :: TVar (Double,Double)
mousePosVar = unsafePerformIO $ newTVarIO (0,0)

mousePos :: Signal (Double,Double)
mousePos = varSignal mousePosVar

keyStateVar :: TVar (Set.Set SDLKey)
keyStateVar = unsafePerformIO $ newTVarIO Set.empty

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

    -- event channel
    (writer, follower) <- atomically $ newWFQueue
    reader <- atomically $ makeWFReader follower

    name <- Draw.makeName
    sig <- execEvent reader (beh name)
    pretime <- SDL.getTicks
    mainLoop writer sig pretime
    TTF.quit
    SDL.quit


mainLoop writer sig pretime = do
    drawing <- atomically $ readSignal sig
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
        forM_ events' $ atomically . writeWFQueue writer 
        posttime <- SDL.getTicks
        let delay :: Int = 1000 * (33 - (fromIntegral posttime - fromIntegral pretime))
        when (delay > 0) $
            threadDelay (fromIntegral delay)
        posttime' <- SDL.getTicks
        mainLoop writer sig posttime'

convertEvent d (SDL.MouseMotion x y _ _) = do
    let pos = convertCoords x y
    atomically $ writeTVar mousePosVar pos
    hits <- getHits d (fromIntegral x) (fromIntegral y)
    return $ Just $ MouseEvent MouseMotion pos hits
convertEvent d (SDL.MouseButtonDown x y but) = do
    hits <- getHits d (fromIntegral x) (fromIntegral y)
    let but' = case but of
         SDL.ButtonLeft  -> Just ButtonLeft
         SDL.ButtonRight -> Just ButtonRight
         _               -> Nothing
    return $ fmap (\b -> 
                MouseEvent (MouseButton b MouseDown) (convertCoords x y) hits
             ) but'
convertEvent d (SDL.MouseButtonUp x y but) = do
    hits <- getHits d (fromIntegral x) (fromIntegral y)
    let but' = case but of
         SDL.ButtonLeft  -> Just ButtonLeft
         SDL.ButtonRight -> Just ButtonRight
         _               -> Nothing
    return $ fmap (\b -> 
                MouseEvent (MouseButton b MouseUp) (convertCoords x y) hits
             ) but'
convertEvent d (SDL.KeyDown sym) = do
    atomically $ do 
        s <- readTVar keyStateVar
        writeTVar keyStateVar $! Set.insert (symKey sym) s
    return $ Just $ KeyDownEvent sym
convertEvent d (SDL.KeyUp   sym) = do
    atomically $ do
        s <- readTVar keyStateVar
        writeTVar keyStateVar $! Set.delete (symKey sym) s
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
