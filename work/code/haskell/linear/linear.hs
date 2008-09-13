{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Typeable
import Data.Array
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Arrow
import Data.Unique

class (Monad m) => Managed m a where
    split :: a -> m (a,a)
    destroy :: a -> m ()

newtype TraceV a = TraceV (Unique, a)
    deriving Typeable

unTraceV (TraceV (u,x)) = x

instance Managed IO (TraceV a) where
    split (TraceV (u,x)) = do
        u1 <- newUnique
        u2 <- newUnique
        let s = show . hashUnique
        putStrLn $ "Split " ++ s u ++ " => (" ++ s u1 ++ ", " ++ s u2 ++ ")"
        return (TraceV (u1,x), TraceV (u2,x))
    destroy (TraceV (u,x)) = do
        putStrLn $ "Destroy " ++ show (hashUnique u)

tr :: a -> IO (TraceV a)
tr x = do
    u <- newUnique
    putStrLn $ "New " ++ show (hashUnique u)
    return (TraceV (u,x))


infixl 9 :*
data Term m where
    TExtern :: (Managed m a, Typeable a) => m a -> Term m
    TVar :: String -> Term m
    TAbs :: String -> Term m -> Term m
    (:*) :: Term m -> Term m -> Term m
    -- split x f = f x x
    TSplit :: Term m
    -- destroy x f = f
    TDestroy :: Term m

type Pad m = Array Int (Val m)
type Code m = Pad m -> m (Val m)

data Val m where
    VExtern :: (Managed m a, Typeable a) => a -> Val m
    VClosure :: Pad m -> (Val m -> Code m) -> Val m
    VNative :: (Val m -> m (Val m)) -> Val m

instance (Monad m) => Managed m (Val m) where
    split (VExtern v) = do
        ~(v1,v2) <- split v
        return (VExtern v1, VExtern v2)
    split (VClosure cl f) = do
        (el1,el2) <- liftM unzip . mapM split . tail $ elems cl
        let (ar1,ar2) = (listArray (bounds cl) (undefined:el1), listArray (bounds cl) (undefined:el2))
        return (VClosure ar1 f, VClosure ar2 f)
    split x@(VNative _) = return (x,x)

    destroy (VExtern v) = destroy v
    destroy (VClosure cl f) = mapM_ destroy . tail $ elems cl
    destroy (VNative _) = return ()
        
parensPrec :: Int -> String -> Int -> String
parensPrec p s prec
    | prec > p = "(" ++ s ++ ")"
    | otherwise = s

-- \x. [prec 0]
-- [prec 1] [prec 2]
showTerm :: Term m -> Int -> String
showTerm (TExtern _) = const "<extern>"
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
    return $ pfx ++ "~" ++ show c

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


type Env = Map.Map String Int

compile :: (Monad m) => Term m -> Env -> Code m
compile (TExtern v) env = const $ liftM VExtern v
compile (TVar v) env = \ar -> return $ ar ! (env Map.! v)
compile (TAbs v t) env = \ar -> do
    let cl = array freebounds $ [ (sub, ar ! sup) | (sup,sub) <- copymap ]
    return $ VClosure cl (\v ar' -> t' (ar' // [(0,v)]))
    where
    frees = zip (Set.toList (Set.delete v (freeVars t))) [1..]
    freemap = Map.fromList $ (v,0):frees
    freebounds = (0,length frees)
    copymap = map (first (env Map.!)) frees
    t' = compile t freemap
compile (f :* x) env = \ar -> do
        f'' <- f' ar
        x'' <- x' ar
        call f'' x''
    where
    f' = compile f env
    x' = compile x env 
compile TSplit env = const . return . VNative $ \x -> return . VNative $ \f -> do
    ~(x1,x2) <- split x
    f' <- call f x1
    call f' x2
compile TDestroy env = const . return . VNative $ \x -> return . VNative $ \f -> do
    destroy x
    return f

call :: (Monad m) => Val m -> Val m -> m (Val m)
call f x = 
    case f of
        VExtern _ -> fail "Cannot call a VExtern (yet?)"
        VNative f' -> f' x
        VClosure cl f' -> f' x cl


run :: forall m a. (Monad m, Typeable a) => Val m -> m a
run (VExtern v) = 
    case cast v of
        Just v' -> return v'
        Nothing -> fail $ "Error: top level cast failure (" ++ show (typeOf v) ++ " -> " ++ show (typeOf (undefined::a)) ++ ")"
run (VClosure _ _) = fail "Error: top level cast failure (closure)"
run (VNative _) = fail "Error: top level cast failure (native)"

test :: (Typeable a) => Term IO -> IO a
test e = do
    putStrLn $ "compiling: " ++ showTerm e 0
    putStrLn "--"
    let lin = evalState (linearize e) 0
    putStrLn $ "linearize: " ++ showTerm lin 0
    putStrLn "--"
    let c = compile lin Map.empty
    putStrLn $ "running..."
    v <- c undefined
    run v
