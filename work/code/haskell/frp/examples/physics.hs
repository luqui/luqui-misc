{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl

main = runGame defaultInit game

game = proc () -> do
    rec world <- integral initWorld -< trajectory world 
                                   ^+^ applyAll (\b -> force world b (0,-0.5)) world
    returnA -< translate (bodyPosition world body) unitCircle
    where
    (body,initWorld) = newBody 1 1 (0,0) (1,0) 0 0 $ emptyWorld
