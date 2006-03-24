import Control.Exception
import Data.List

type Integrator a = a -> a -> (a -> a) -> a

simpsonsRule :: (Fractional a) => Integrator a
simpsonsRule lo hi f = (hi - lo)/6 * (f lo + 4*f ((lo + hi)/2) + f hi)

-- We evaluate f^(4)(x) at a, since we assume that a will always
-- be the least of the endpoints.
simpsonsLnError :: (Fractional a) => a -> a -> a
simpsonsLnError a b = (((b - a)/2)^5 / 90) * (6 / a^4)

trapezoidalRule :: (Fractional a) => Integrator a
trapezoidalRule lo hi f = (hi - lo)/2 * (f lo + f hi)

-- We evaluate f''(x) at a, since we assume that a will always be
-- the least of the endpoints.
trapezoidalLnError :: (Fractional a) => a -> a -> a
trapezoidalLnError a b = ((b - a)^3 / 12) * (1 / a^2)

midpointRule :: (Fractional a) => Integrator a
midpointRule lo hi f = 2 * (hi - lo)/2 * f ((hi + lo)/2)

midpointLnError :: (Fractional a) => a -> a -> a
midpointLnError a b = (((b - a)/2)^3 / 3) * (1 / a^2)

multiIntegrate :: (Fractional a) => Int -> Integrator a -> Integrator a
multiIntegrate pts int lo hi f = 
    sum $ map (\x -> int x (x+step) f)
        $ map (\n -> step * fromIntegral n + lo) [0..pts-1]
    where step = (hi-lo) / fromIntegral pts

multiError :: (Fractional a) => Int -> (a -> a -> a) -> a -> a -> a
multiError pts err lo hi =
    sum $ map (\x -> err x (x+step)) 
        $ map (\n -> step * fromIntegral n + lo) [0..pts-1]
    where step = (hi-lo) / fromIntegral pts

rules = [ ("simpsons",    (simpsonsRule,    simpsonsLnError)),
          ("trapezoidal", (trapezoidalRule, trapezoidalLnError)),
          ("midpoint",    (midpointRule,    midpointLnError)) ]

ask :: (Read a) => String -> IO a
ask q = 
    handle (const (ask q)) $ do
        putStr q
        readLn

askStr :: (String -> Maybe a) -> String -> IO a
askStr f q = do
    putStr q
    str <- getLine
    maybe (askStr f q) return (f str)

main :: IO ()
main = do
    putStrLn "Integrating ln(x) over [a,b]"
    a <- ask "a = "
    b <- ask "b = "
    (method,error) <- askStr (`lookup` rules) $ 
            "What method (" ++ concat (intersperse ", " $ map fst rules) ++ ")? "
    pts <- ask "How many points? "
    let approx = multiIntegrate pts method a b log
    let actual = b * log b - b - a * log a + a
    let bound = abs $ multiError pts error a b
    putStrLn $ "output = " ++ show approx
    putStrLn $ "error = " ++ show (abs (approx - actual))
    putStrLn $ "error bound = " ++ show bound

-- vim: expandtab :
