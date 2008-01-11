module Fregl.SDLCore where

import Data.Maybe
import Control.Monad
import Control.Applicative
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU
import qualified Graphics.UI.SDL as SDL
import qualified Fregl.Event
import Fregl.Event hiding (Event)
import Fregl.Signal
import Fregl.Vector
import Fregl.LinearSplit
import qualified Fregl.Drawing as Draw
import Data.List

data EventSDL
    = TimestepEvent Double
    | MouseEvent MouseEvent Vec2

data MouseEvent
    = MouseButtonDown SDL.MouseButton [GL.Name]
    | MouseButtonUp   SDL.MouseButton [GL.Name]
    | MouseMotion

type Event    = Fregl.Event.Event EventSDL

waitTimestep :: Event Double
waitTimestep = do
    e <- waitEvent
    case e of
         TimestepEvent dt -> return dt
         _ -> waitTimestep

waitClick :: Event Vec2
waitClick = do
    e <- waitEvent
    case e of
         MouseEvent (MouseButtonDown _ _) pos -> return pos
         _ -> waitClick

waitClickName :: Draw.Name -> Event ()
waitClickName n = do
    n' <- unsafeEventIO $ readLinearSplit $ Draw.getName n
    waitClickName' n'
    where
    waitClickName' n' = do
        e <- waitEvent
        case e of
             MouseEvent (MouseButtonDown _ names) _
                | n' `elem` names -> return ()
             _ -> waitClickName' n'

integral :: Double -> Signal Double -> Event (Signal Double)
integral init sig = pure init `untilEvent` wait
    where
    wait = do
        dt <- waitTimestep
        v <- readSig sig
        integral (init + dt * v) sig
    

runGame :: (Draw.Name -> Event (Signal Draw.Drawing)) -> IO ()
runGame beh = do
    -- set up SDL
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    name <- Draw.makeName
    cxt <- newEventCxt (beh name)
    pretime <- SDL.getTicks
    mainLoop cxt pretime
    SDL.quit

    where

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

        -- poll for events
        events <- whileM (/= SDL.NoEvent) SDL.pollEvent
        when (not $ any isQuitEvent events) $ do
            events' <- catMaybes <$> mapM (convertEvent drawing) events
            cxt' <- foldM (\cx ev -> nextEventCxt ev cx) cxt events'
            posttime <- SDL.getTicks
            let timediff = fromIntegral (posttime - pretime) / 1000
            cxt'' <- nextEventCxt (TimestepEvent timediff) cxt'
            mainLoop cxt'' posttime

    convertEvent _ (SDL.MouseMotion x y _ _) = return $
        Just $ MouseEvent MouseMotion (convertCoords x y)
    convertEvent d (SDL.MouseButtonDown x y but) = do
        hits <- getHits d (fromIntegral x) (fromIntegral y)
        return $ Just $ MouseEvent (MouseButtonDown but hits) (convertCoords x y)
    convertEvent d (SDL.MouseButtonUp x y but) = do
        hits <- getHits d (fromIntegral x) (fromIntegral y)
        return $ Just $ MouseEvent (MouseButtonUp but hits) (convertCoords x y)
    convertEvent _ _ = return $ Nothing

    getHits drawing x y = do
        ((), recs) <- GL.getHitRecords 64 $ do
            viewport <- GL.get GL.viewport
            GL.matrixMode GL.$= GL.Projection
            GL.loadIdentity
            GLU.pickMatrix (x,y) (1,1) viewport
            initGLMatrix
            GL.matrixMode GL.$= GL.Modelview 0
            Draw.runDrawing drawing
        return $ case recs of
            Nothing -> []
            Just hits -> nub $ concatMap (\(GL.HitRecord _ _ ns) -> ns) hits

    convertCoords x y = ( 32 * fromIntegral x / 640 - 16
                        , 24 * fromIntegral y / 480 - 12
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
