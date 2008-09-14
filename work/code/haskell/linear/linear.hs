{-# OPTIONS_GHC -fglasgow-exts -fno-monomorphism-restriction #-}

import Data.Typeable
import Data.Array
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Arrow
import Data.Unique
import Control.Monad.Writer
import Control.Monad
import Data.List


infixl 9 :*
data Term m where
    TLit :: String -> Term m
    TVar :: String -> Term m
    TAbs :: String -> Term m -> Term m
    (:*) :: Term m -> Term m -> Term m
    -- split x f = f x x
    TSplit :: Term m
    -- destroy x f = f
    TDestroy :: Term m

parensPrec :: Int -> String -> Int -> String
parensPrec p s prec
    | prec > p = "(" ++ s ++ ")"
    | otherwise = s

-- \x. [prec 0]
-- [prec 1] [prec 2]
showTerm :: Term m -> Int -> String
showTerm (TLit s)    = const $ "<" ++ s ++ ">"
showTerm (TVar v)    = const v
showTerm (TAbs v t)  = parensPrec 0 $ "\\" ++ v ++ ". " ++ showTerm t 0
showTerm (f :* x)    = parensPrec 1 $ showTerm f 1 ++ " " ++ showTerm x 2
showTerm TSplit      = const "split"
showTerm TDestroy    = const "destroy"

freeVars :: Term m -> Set.Set String
freeVars (TVar v)    = Set.singleton v
freeVars (TAbs v t)  = Set.delete v (freeVars t)
freeVars (f :* x)    = freeVars f `Set.union` freeVars x
freeVars _           = Set.empty

subst :: String -> Term m -> Term m -> Term m
subst v for e@(TVar v')
    | v == v' = for
    | otherwise = e
subst v for e@(TAbs v' t)
    | v == v' = e
    | otherwise = TAbs v' (subst v for t)
subst v for (f :* x) = subst v for f :* subst v for x
subst v for e = e

type Supply = State Int

fresh :: String -> Supply String
fresh pfx = do
    c <- get
    put $! c+1
    return $ pfx ++ "_" ++ show c

linearize :: Term m -> Supply (Term m)
linearize v@(TVar _) = return v
linearize (TAbs v t) = do
    t' <- linearize t
    return $ if v `Set.member` freeVars t'
             then TAbs v t'
             else TAbs v (TDestroy :* TVar v :* t')
linearize (f :* x) = do
    f' <- linearize f
    x' <- linearize x
    let shared = freeVars f' `Set.intersection` freeVars x'
    elim (Set.toList shared) (f',x')
    where
    elim [] (f,x) = return $ f :* x
    elim (v:vs) (f,x) = do
        v1 <- fresh v
        v2 <- fresh v
        r <- elim vs (subst v (TVar v1) f, subst v (TVar v2) x)
        return $ TSplit :* TVar v :* (TAbs v1 $ TAbs v2 $ r)
linearize e = return e

type Output = String
type Compile = WriterT Output Supply

output = tell

forM_ = flip mapM_
intercalate s = concat . intersperse s

compile :: Term m -> Compile String
compile (TLit s) = return s
compile (TVar v) = return v
compile (TAbs v t) = do
    stname <- lift $ fresh "C_"
    body <- compile t
    let freevars = Set.toList (Set.delete v (freeVars t))
    output $ "struct " ++ stname ++ " : public Closure {\n"
          ++ "    Val* call(Val* " ++ v ++ ") {\n"
          ++ "        Val* _result = " ++ body ++ ";\n"
          ++ "        delete this;\n"
          ++ "        return _result;\n"
          ++ "    }\n"
          ++ "    void clone(Val*& _L, Val*& _R) {\n"
    forM_ freevars $ \v -> do
        output $ "        Val* " ++ v ++ "_R;\n"
              ++ "        " ++ v ++ "->clone(" ++ v ++ ", " ++ v ++ "_R);\n"
    output $ "        _L = this;\n"
          ++ "        _R = new " ++ stname ++ "(" ++ intercalate "," (map (++ "_R") freevars) ++ ");\n"
          ++ "    }\n"
          ++ "    void destroy() {\n"
    forM_ freevars $ \v -> do
          output $  "        " ++ v ++ "->destroy();\n"
    output $ "        delete this;\n"
          ++ "    }\n"
    forM_ freevars $ \v -> do
        output $ "    Val* " ++ v ++ ";\n"
    output $ "    " ++ stname ++ "(" ++ intercalate "," (map (\v -> "Val* " ++ v) freevars) ++ ")\n"
    when (not (null freevars)) $
        output $ "      : " ++ intercalate "," (map (\v -> v ++ "(" ++ v ++ ")") freevars) ++ "\n"
    output $ "    { }\n"
          ++ "};\n\n"
    return $ "(new " ++ stname ++ "(" ++ intercalate "," freevars ++ "))"
compile (f :* x) = do
    f' <- compile f
    x' <- compile x
    return $ "((Closure*)" ++ f' ++ ")->call(" ++ x' ++ ")"
compile TSplit = return "SPLIT"
compile TDestroy = return "DESTROY"

runCompile :: Term m -> String
runCompile t = "#include \"prelude.h\"\n"
            ++ head
            ++ "int main () {\n"
            ++ "    std::cout << ((Int*)" ++ main ++ ")->getdata() << \"\\n\";\n"
            ++ "    return 0;\n"
            ++ "}\n"
    where (main,head) = evalState (runWriterT (compile =<< lift (linearize t))) 0




fixT = TAbs "f" $ TAbs "x" (TVar "f" :* (TVar "x" :* TVar "x")) :* TAbs "x" (TVar "f" :* TVar "x" :* TVar "x")
idT = TAbs "x" (TVar "x")
constT = TAbs "x" $ TAbs "y" $ TVar "x"
