import Fregl.SDL
import qualified Fregl.Drawing as Draw


mousePos :: Ev (Signal Vec2)
mousePos = mousePos' (0,0)
    where
    mousePos' init = pure init `untilEvent` (waitMouseMotion >>= mousePos')

main = runGameSDL $ \_ -> do
    mousepos <- mousePos
    p <- loopSignal $ \p ->
        integral vzero =<< integral vzero (liftA2 force mousepos p)
    return $ Draw.translate <$> p <*> pure Draw.circle
    
    where
    force mouse p = 20 *^ (mouse ^-^ p) ^/ norm2 (mouse ^-^ p)
