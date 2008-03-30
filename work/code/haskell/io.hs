import Control.Concurrent

data IOTree 
    = PutChar Char
    | GetChar (Char -> IOTree)
    | Seq IOTree IOTree
    | Noop


interpIOTree :: IOTree -> IO ()
interpIOTree (PutChar ch) = putChar ch
interpIOTree (GetChar f)  = do
    ch <- getChar
    interpIOTree (f ch)
interpIOTree (Seq a b) = interpIOTree a >> interpIOTree b
interpIOTree (Noop) = return ()


putStrIOTree :: String -> IOTree
putStrIOTree [] = Noop
putStrIOTree (c:cs) = PutChar c `Seq` putStrIOTree cs


getLineIOTree :: (String -> IOTree) -> IOTree
getLineIOTree f = getLineIOTree' id
    where
    getLineIOTree' s = GetChar $ \ch ->
        case ch of
             '\n' -> f (s "")
             _    -> getLineIOTree' $ s . (ch :)


-- now we hoist the CPS-style IOTree into a monad

newtype IO' a = IO' { runIO' :: (a -> IOTree) -> IOTree }

instance Functor IO' where
    fmap f (IO' c) = IO' (c . (. f))

instance Monad IO' where
    return x = IO' ($ x)
    IO' m >>= f = IO' $ \c -> m (\a -> runIO' (f a) c)

interpIO' :: IO' () -> IO ()
interpIO' (IO' f) = interpIOTree $ f (\() -> Noop)

putCharIO' :: Char -> IO' ()
putCharIO' ch = IO' (\f -> PutChar ch `Seq` f ())

putStrIO' :: String -> IO' ()
putStrIO' [] = return ()
putStrIO' (x:xs) = putCharIO' x >> putStrIO' xs

getCharIO' :: IO' Char
getCharIO' = IO' (\f -> GetChar f)

getLineIO' :: IO' String
getLineIO' = getCharIO' >>= \ch -> 
    case ch of
         '\n' -> return ""
         _    -> fmap (ch:) getLineIO'

