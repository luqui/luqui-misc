import Fregl.SDL
import qualified Fregl.Drawing as Draw
import Fregl.Event

main = do
    runGameSDL $ \_ -> do
        stick <- unsafeEventIO $ Draw.imageToSprite "res/turquoise_stick.png"
        reddy <- unsafeEventIO $ Draw.imageToSprite "res/red_on_white.png"
        return $ pure $ Draw.sprite stick 
              `mappend` Draw.translate (4,0) (Draw.sprite reddy)
