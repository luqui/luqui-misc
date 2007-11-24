{-# OPTIONS_GHC -fglasgow-exts -fth #-}

import Accessor
import Control.Monad.State

data Foo =
    Foo { foo_ :: Int
        , bar_ :: Int }
    deriving Show

-- make accessors for records ending in an underscore
$(deriveAccessors ''Foo)

main :: IO ()
main = flip evalStateT (Foo 0 0) $ do
    get >>= liftIO . print
    foo =: 4
    get >>= liftIO . print
    modA foo (\x -> x * 2 + 1)
    get >>= liftIO . print
