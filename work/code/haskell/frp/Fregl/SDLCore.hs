module Fregl.SDLCore where

import Data.Maybe
import Control.Monad
import qualified Graphics.Rendering.OpenGL.GL as GL
import qualified Graphics.Rendering.OpenGL.GLU as GLU
import qualified Graphics.UI.SDL as SDL
import qualified Fregl.Event
import Fregl.Event hiding (Event, Behavior)
import Fregl.Signal
import Fregl.Vector
import Fregl.Drawing

data EventSDL
    = TimestepEvent Double
    | MouseEvent MouseEvent Vec2

data MouseEvent
    = MouseButtonDown SDL.MouseButton
    | MouseButtonUp   SDL.MouseButton
    | MouseMotion

type Event    = Fregl.Event.Event EventSDL
type Behavior = Fregl.Event.Behavior EventSDL

runGame :: Behavior Drawing -> IO ()
runGame beh = do
    -- set up SDL
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    -- set up OpenGL
    GL.matrixMode GL.$= GL.Projection
    GL.loadIdentity
    GLU.ortho2D (-16) 16 (-12) 12
    GL.matrixMode GL.$= GL.Modelview 0
    GL.loadIdentity

    cxt <- newEventCxt beh
    pretime <- SDL.getTicks
    mainLoop cxt pretime
    SDL.quit

    where

    mainLoop cxt pretime = do
        let drawing = readEventCxt cxt
        -- draw it
        GL.clear [GL.ColorBuffer]
        runDrawing drawing
        SDL.glSwapBuffers

        -- poll for events
        events <- whileM (/= SDL.NoEvent) SDL.pollEvent
        when (not $ any isQuitEvent events) $ do
            let events' = catMaybes $ map convertEvent events
            cxt' <- foldM (\cx ev -> nextEventCxt ev cx) cxt events'
            posttime <- SDL.getTicks
            let timediff = fromIntegral (posttime - pretime) / 1000
            cxt'' <- nextEventCxt (TimestepEvent timediff) cxt'
            mainLoop cxt'' posttime

    convertEvent (SDL.MouseMotion x y _ _) = 
        Just $ MouseEvent MouseMotion (convertCoords x y)
    convertEvent (SDL.MouseButtonDown x y but) =
        Just $ MouseEvent (MouseButtonDown but) (convertCoords x y)
    convertEvent (SDL.MouseButtonUp x y but) = 
        Just $ MouseEvent (MouseButtonUp but) (convertCoords x y)
    convertEvent _ = Nothing

    convertCoords x y = ( 32 * fromIntegral x / 640 - 16
                        , 24 * fromIntegral y / 480 - 12
                        )

    isQuitEvent SDL.Quit = True
    isQuitEvent (SDL.KeyDown (SDL.Keysym { SDL.symKey = SDL.SDLK_ESCAPE })) = True
    isQuitEvent _ = False

whileM :: (a -> Bool) -> IO a -> IO [a]
whileM cond action = do
    v <- action
    if cond v
       then fmap (v:) $ whileM cond action
       else return []
