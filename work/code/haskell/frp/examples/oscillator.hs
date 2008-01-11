import Fregl.SDL
import qualified Fregl.Drawing as Draw

main = runGameSDL $ \nm -> do
    e <- loopSignal (0,0) $ \s'' -> do
        s' <- integral (0,2) s'' 
        s <- integral (10,0) $ fmap ((-1) *^) s'
        return $ s
    e' <- e `untilEvent` (waitClickName ButtonLeft MouseDown nm >> return (pure vzero))
    return $ fmap (\x -> Draw.translate x (Draw.name nm Draw.circle)) e'
