{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl.SDL
import qualified Fregl.Drawing as Draw
import Fregl.Event

main = do
    runGameSDL $ \_ -> do
        stick <- loadImage "res/turquoise_stick.png"
        reddy <- loadImage "res/red_on_white.png"
        time' <- time
        return $ fromSP $ proc () -> do
            t <- sigSP time' -< ()
            returnA -< mconcat
                [ Draw.sprite stick 
                , Draw.translate (4,0) $ Draw.sprite reddy
                , Draw.translate (0,8-t) $ Draw.scale 40 40 $ Draw.text "Hello, World"
                ]
