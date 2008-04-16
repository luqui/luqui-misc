{-# LANGUAGE GADTs #-}

data IO' a where
    PutChar  :: Char -> IO' ()
    GetChar  :: IO' Char
    Sequence :: IO' a -> (a -> IO' b) -> IO' b
    Value    :: a -> IO' a

oldSequence m f = Sequence m (\_ -> f)

putStr' str = foldr1 oldSequence (map PutChar str)

getLine' = 
    Sequence GetChar (\ch ->
        if ch == '\n' then
            Value []
        else
            Sequence getLine' (\rest ->
                Value (ch : rest)))

main' = Sequence (putStr' "Enter your name\n") (\_ ->
        Sequence getLine' (\line ->
        putStr' ("Your name is " ++ line ++ "\n")))

main = interp main'











interp :: IO' a -> IO a
interp (PutChar ch)   = putChar ch
interp GetChar        = getChar
interp (Sequence m f) = interp m >>= interp . f
interp (Value x)      = return x
