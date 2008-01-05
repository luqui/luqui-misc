import Debug.Trace

type Time = Double
data Signal a 
    = Signal a (Time -> Signal a)

instance Functor Signal where
    fmap f ~(Signal x cont) = Signal (f x) (fmap f . cont)

integral :: Double -> Signal Double -> Signal Double
integral init ~(Signal x cont) = 
    Signal init (\dt -> integral (trace "add" $ init + dt*x) $ cont dt)

runSignal :: Double -> Signal a -> [a]
runSignal step (Signal x cont) = x : runSignal step (cont step)

listSignal :: Double -> [a] -> Signal a
listSignal step = listSignal' 0
    where
    listSignal' offs list@(x:xs)
        | offs < 0 = listSignal' (offs + step) xs
        | otherwise =
            Signal x $ \dt -> listSignal' (offs-dt) list

buffer :: Double -> Signal a -> Signal a
buffer step = listSignal step . runSignal step

ex :: Signal Double
ex = buffer 0.05 $ integral 1 ex
