{-# OPTIONS_GHC -fglasgow-exts #-}

import Fregl.SDL
import qualified Fregl.Drawing as Draw

main = runGameSDL $ \nm -> mdo
    e <- do
        v <- integral (0,2) $ ((-1) *^) <$> e
        integral (10,0) v
    e' <- e `untilEvent` (waitClickName ButtonLeft MouseDown nm >> return (pure vzero))
    return $ Draw.translate <$> e' <*> pure (Draw.name nm Draw.circle)
