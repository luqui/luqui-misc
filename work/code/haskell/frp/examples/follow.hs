{-# OPTIONS_GHC -fglasgow-exts #-}

import Fregl.SDL
import qualified Fregl.Drawing as Draw

main = runGameSDL $ \_ -> mdo
    p <- integral vzero =<< integral vzero (liftA2 force mousePos p)
    return $ Draw.translate <$> p <*> pure Draw.circle
    
    where
    force mouse p = 20 *^ (mouse ^-^ p) ^/ norm2 (mouse ^-^ p)
