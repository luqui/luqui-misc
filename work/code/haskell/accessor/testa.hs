{-# OPTIONS_GHC -fglasgow-exts -fth #-}

import Accessor

data Foo =
    Foo { foo_ :: Int
        , bar  :: Int }
    deriving Show

$(deriveAccessors ''Foo)
