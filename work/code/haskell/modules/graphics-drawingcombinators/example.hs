import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.SDL as SDL

initScreen :: IO ()
initScreen = do
    SDL.init [SDL.InitTimer, SDL.InitVideo]
    -- resolution & color depth
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]
    return ()


drawing :: Draw.Draw ()
drawing = Draw.translate (0.0,0.2) $ Draw.scale 0.3 0.3 $ Draw.color (1,0,0,0) Draw.circle

main :: IO ()
main = do
    initScreen
    Draw.draw drawing
    SDL.glSwapBuffers
    untilM (== SDL.Quit) SDL.waitEvent
    SDL.quit
    return ()

untilM :: (Monad m) => (a -> Bool) -> m a -> m a
untilM f m = do
    x <- m
    if f x then return x else untilM f m 
