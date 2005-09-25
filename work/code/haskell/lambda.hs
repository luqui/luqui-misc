{-# OPTIONS_GHC -fglasgow-exts #-}

-- Solving the Expression Problem in Haskell

import Control.Monad.Reader
import Data.Map as Map

type Var = String

data Lambda lx = Lambda Var lx
               | LApp lx lx
               | LVar Var
    deriving Show

type Pad lx = Map.Map String lx
type Eval lx = Reader (Pad lx) lx

class LambdaBase lx where
    promote :: Lambda lx -> lx
    demote  :: lx -> Maybe (Lambda lx)
    eval    :: lx -> Eval lx


evalBase :: (LambdaBase lx) => Lambda lx -> Eval lx
evalBase app@(LApp f val) = maybe (return (promote app))
                                       (\(Lambda var exp) -> local (Map.insert var val) (eval exp))
                                       (demote f)
evalBase (LVar var) = do
    pad <- ask 
    return (pad ! var)
evalBase exp = return (promote exp)


data LX = LX (Lambda LX)
    deriving Show

instance LambdaBase LX where
    promote lam     = LX lam
    demote (LX lam) = Just lam
    eval (LX lam)   = evalBase lam

run :: LX -> LX
run lam = runReader (eval lam) Map.empty
