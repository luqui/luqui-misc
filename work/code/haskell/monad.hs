
data Apply a = Apply a

instance Monad Apply where
    Apply x >>= f   =   f x
    return          =   Apply

mul2 :: (Num a) => Apply a -> Apply a
mul2 x = do
    orig <- x
    return (2 * orig)

printApply :: (Show a) => Apply a -> IO ()
printApply (Apply x) = print x

main :: IO ()
main = printApply $ mul2 $ Apply 8
