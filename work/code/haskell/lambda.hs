import Control.Monad.Reader
import Debug.Trace

type Var = Int

data Lambda = Lambda Lambda
            | App Lambda Lambda
            | Term Var
    deriving Show

type PadStack = [Lambda]
type Eval = Reader PadStack Lambda

eval :: Lambda -> Eval
eval (App f exp) = do
    lam <- eval f
    case lam of
        Lambda body -> local (body:) $ eval exp
        _           -> error "diverging expression"
eval (Term var) = do
    stack <- ask
    return $ stack !! var
eval lam@(Lambda _) = return lam

reduce :: Lambda -> Lambda
reduce lam = runReader (eval lam) []
