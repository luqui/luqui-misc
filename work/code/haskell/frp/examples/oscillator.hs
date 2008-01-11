import Fregl.SDL
import qualified Fregl.Drawing as Draw

main = runGameSDL $ \nm -> do
    e <- loopSignal 0 $ \s'' -> do
        s' <- integral 0 s'' 
        s <- integral 10 s'
        return (negate <$> s)
    e' <- e `untilEvent` (waitClickName ButtonLeft MouseDown nm >> return (pure 0))
    return $ fmap (\x -> Draw.translate (x,0) (Draw.name nm Draw.circle)) e'
