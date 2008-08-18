import qualified Graphics.UI.SDL as SDL

import SecularFRP.Stream
import SecularFRP.Event
import SecularFRP.Behavior

type Event = EventF SDL.Event
type Behavior = BehaviorF SDL.Event

joinMaybes :: Event (Maybe a) -> Event a
joinMaybes = EventF . go . runEventF
    where
    go (Read f) = Read (go . f)
    go (Write (t,Nothing) sf) = adjust' (-t) (go sf)
    go (Write (t,Just x) sf) = Write (t,x) (go sf)

mousePos :: Event (Int,Int)
mousePos = joinMaybes (fmap filt idE)
    where
    filt (SDL.MouseMotion x y _ _) = Just (fromIntegral x,fromIntegral y)
    filt _ = Nothing



runFRP :: Event String -> IO ()
runFRP e = do
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    mainLoop (runEventF e)

  where
    mainLoop (Read i) = do
        e <- SDL.waitEvent
        t <- SDL.getTicks
        mainLoop (i (fromIntegral t, e))
    mainLoop (Write (t,o) sf) = putStrLn (show t ++ ": " ++ o) >> mainLoop sf

main = runFRP (fmap show mousePos)
