{-# OPTIONS_GHC -fglasgow-exts -fth #-}

module Accessor
    (Accessor, accessor, readVal, writeVal) 
where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad.State

data Accessor s a
    = Accessor { readVal  :: forall m. (MonadState s m) => m a
               , writeVal :: forall m. (MonadState s m) => a -> m ()
               }

wtfmap :: Monad m => (a -> b) -> m a -> m b
wtfmap f m = m >>= (return . f)

accessor :: Name -> Q Exp
accessor name = [|
    Accessor { readVal  = wtfmap $( return $ VarE name ) get
             , writeVal = \n -> 
                get >>= \s -> 
                    put $( return $ RecUpdE (VarE 's) [(name, VarE 'n)] )
             }
    |]
