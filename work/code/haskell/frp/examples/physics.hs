{-# OPTIONS_GHC -fglasgow-exts -farrows #-}

import Fregl

main = runGame defaultInit game

game = proc () -> do
    rec world <- integral initWorld -< trajectory world
    returnA -< translate (bodyPosition world body) unitCircle
    where
    (body,initWorld) = newBody 1 1 (0,0) (1,0) 0 0 $ emptyWorld
