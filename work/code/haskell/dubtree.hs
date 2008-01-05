import Debug.Trace

data Dub a
    = Dub { dubStep  :: Double
          , dubChild :: [Dub a]
          , dubNext  :: Dub a
          , dubVal   :: a
          }

instance Functor Dub where
    fmap f (Dub step child next x) = Dub step (map (fmap f) child) (fmap f next) (f x)

class (Functor w) => Comonad w where
    pull   :: w a -> a
    (=>>)  :: w a -> (w a -> b) -> w b
    cojoin :: w a -> w (w a)

    w =>> f = fmap f (cojoin w)
    cojoin w = w =>> id

instance Comonad Dub where
    pull = dubVal
    cojoin dub = Dub { dubStep = dubStep dub
                     , dubNext = cojoin (dubNext dub)
                     , dubChild = map cojoin (dubChild dub)
                     , dubVal = dub
                     }

dub :: Dub Double
dub = makeDub 0
    where
    makeDub n = makeTree n 1 (makeDub (n+1))
    makeTree n step next = 
        -- child = [ makeTree (n+step/2) (step/2) next
        --         , makeTree (n+step/4) (step/4) (child !!0)
        --         , ...
        --         ]
        let child = zipWith (\st nx -> makeTree (n+st) st nx)
                            (childSteps step) nexts
            nexts = next:child
        in 
        Dub { dubStep = step
            , dubChild = child
            , dubNext = next
            , dubVal = n
            }

childSteps :: Double -> [Double]
childSteps s = iterate (/2) (s/2)

advanceDub :: Double -> Double -> Dub a -> Dub a
advanceDub tol step dub
    | step < dubStep dub = advanceDown step dub
    | otherwise = advanceDub tol (step - dubStep dub) (dubNext dub)
    where
    advanceDown step dub
        | step < tol = dub
        | otherwise = 
            let child:_ = until (\(d:_) -> dubStep d <= step) tail (dubChild dub)
            in advanceDown (step - dubStep child) child

foldDub :: (Double -> a -> b -> b) -> b -> Dub a -> Dub b
foldDub f init (Dub step child next a) =
    Dub { dubStep  = step
        , dubChild = zipWith (\s ch -> foldDub f (f s a init) ch) 
                             (childSteps step) child
        , dubNext  = foldDub f (f step a init) next
        , dubVal   = init
        }

integral :: Double -> Dub Double -> Dub Double
integral = foldDub (\s x cur -> cur + s*x)

dubToList :: Double -> Dub a -> [a]
dubToList step dub = dubVal dub : dubToList step (advanceDub step step dub)
