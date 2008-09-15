
type Time = Double
data StepFun a = StepFun { sfTime :: Double, sfVal :: a, sfRest :: StepFun a }
newtype BB a = BB { runBB :: Time -> StepFun a }

-- BB = Behavior . Behavior  (or rather Behavior . Reactive)

instance Functor StepFun where
    fmap f (StepFun t0 x rest) = StepFun t0 (f x) (fmap f rest)
instance Functor BB where
    fmap f (BB t) = BB (fmap f . t)

infinity = 1/0 :: Time

instance Monad BB where
    return x = BB $ \t -> StepFun t x (StepFun infinity undefined undefined)
    m >>= f = joinBB (fmap f m)

untilSF :: StepFun a -> Time -> StepFun a -> StepFun a
untilSF (StepFun t0 x0 rest0) t1 other
    | t0 <= t1   = StepFun t0 x0 (untilSF rest0 t1 other)
    | otherwise  = other

joinBB :: BB (BB a) -> BB a
joinBB f = BB $ \t -> go (runBB f t)
    where
    go b = let subsf = runBB (sfVal b) (sfTime b)
               rest  = sfRest b in
           untilSF subsf (sfTime rest) (go rest)


seconds :: BB Time
seconds = BB $ \t -> go t
    where
    go t = t `seq` StepFun t (fromIntegral (floor t)) (go (fromIntegral (floor t + 1)))

inspectBB :: (Show a) => StepFun a -> IO ()
inspectBB (StepFun t0 x0 rest) = do
    putStrLn $ show t0 ++ " : " ++ show x0
    putStr "Continue? "
    c <- getChar
    putStrLn ""
    if c == 'n'
       then return ()
       else inspectBB rest
