{- 
maternalGrandfather :: Sheep -> Maybe Sheep
maternalGrandfather s = do m <- mother s
                           father m
-}

maternalGrandfather :: Sheep -> Maybe Sheep
maternalGrandfather s = mother s >>= father

{-
fathersMaternalGrandmother :: Sheep -> Maybe Sheep
fathersMaternalGrandmother s = do f  <- father s
                                  gm <- mother f
                                  mother gm
-}

fathersMaternalGrandmother :: Sheep -> Maybe Sheep
fathersMaternalGrandmother s = father s >>= mother >>= mother

{-
mothersPaternalGrandfather :: Sheep -> Maybe Sheep
mothersPaternalGrandfather s = do m  <- mother s
                                  gf <- father m
                                  father gf
-}

mothersPaternalGrandfather :: Sheep -> Maybe Sheep
mothersPaternalGrandfather s = mother s >>= father >>= father
