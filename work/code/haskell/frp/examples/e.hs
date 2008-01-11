import Fregl.SDLCore
import Fregl.Drawing
import Fregl.Event
import Control.Applicative

main = runGame $ \nm -> do
    e <- loopSignal 0 $ \s'' -> do
        s' <- integral 0 s'' 
        s <- integral 10 s'
        return (fmap negate s)
    e' <- e `untilEvent` (waitClickName nm >> return (pure 0))
    return $ fmap (\x -> translate (x,0) (name nm circle)) e'
