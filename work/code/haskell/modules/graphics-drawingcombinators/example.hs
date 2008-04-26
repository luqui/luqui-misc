import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.SDL as SDL

resX = 640
resY = 480

initScreen :: IO ()
initScreen = do
    SDL.init [SDL.InitTimer, SDL.InitVideo]
    -- resolution & color depth
    SDL.setVideoMode resX resY 32 [SDL.OpenGL]
    return ()


drawing :: Draw.Draw ()
drawing = Draw.translate (0.0,0.2) $ Draw.scale 0.3 0.3 $ Draw.color (1,0,0,0) Draw.circle

main :: IO ()
main = do
    initScreen
    Draw.draw drawing
    SDL.glSwapBuffers
    waitClicks
    SDL.quit
    return ()

    where
    waitClicks = do
        ev <- SDL.waitEvent
        case ev of
             SDL.Quit -> return ()
             SDL.MouseButtonDown x y _ -> do
                 let x' = 2*(fromIntegral x / fromIntegral resX) - 1
                 let y' = 1 - 2*(fromIntegral y / fromIntegral resY)
                 hit <- Draw.click (x',y') drawing
                 case hit of
                      Nothing -> waitClicks
                      Just () -> putStrLn "Hit!" >> waitClicks
             _ -> waitClicks

untilM :: (Monad m) => (a -> Bool) -> m a -> m a
untilM f m = do
    x <- m
    if f x then return x else untilM f m 
