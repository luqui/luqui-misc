import Fregl.SDL
import qualified Fregl.Drawing as Draw
import Fregl.Event

main = do
    runGameSDL $ \_ -> do
        stick <- unsafeEventIO $ Draw.imageToSprite "res/turquoise_stick.png"
        return $ pure $ Draw.sprite stick
