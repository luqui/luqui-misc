{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace

data Type where
    TAtom  :: String             -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type       -> Type  -- functions
    TTuple :: Type -> Type       -> Type  -- tuples
    TVar   :: Integer            -> Type  -- type variable
    TInf   :: Integer -> Type -> [Equation] -> Type  -- universal type
    TSup   :: Integer -> Type -> [Equation] -> Type  -- existential type
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar v)     = show v
    show (TInf i t cons)   = "^" ++ show i ++ " " ++ show t ++ " " ++ show cons
    show (TSup i t cons)   = "v" ++ show i ++ " " ++ show t ++ " " ++ show cons

type Subst = Map.Map Type Type
type SubstID = Integer

data Equation where
    (:<) :: Type -> Type -> Equation
    deriving (Eq,Ord)

instance Show Equation where
    show (a :< b) = show a ++ " <: " ++ show b


substituteType :: Subst -> Type -> Type
substituteType sub x
    | x `Map.member` sub = sub Map.! x
substituteType sub (TArrow a b) 
    = TArrow (substituteType sub a) (substituteType sub b)
substituteType sub (TTuple a b) 
    = TTuple (substituteType sub a) (substituteType sub b)
substituteType sub (TInf v t cons) 
    = TInf v (substituteType subst t) (map (substituteEquation subst) cons)
    where
    subst = Map.delete (TVar v) sub
substituteType sub (TSup v t cons) 
    = TSup v (substituteType subst t) (map (substituteEquation subst) cons)
    where
    subst = Map.delete (TVar v) sub
substituteType _ x = x

substituteEquation :: Subst -> Equation -> Equation
substituteEquation sub (a :< b) = substituteType sub a :< substituteType sub b


forEach :: (Monad m, Ord a) => Set.Set a -> (a -> m ()) -> m ()
forEach set action = Set.fold (\item m -> m >> action item) (return ()) set


data ComputeState where
    ComputeState 
        { varCounter    :: Integer
        , seenSet       :: Set.Set Equation
        } :: ComputeState

type Compute a = StateT ComputeState (ReaderT Int IO) a

allocateVar :: Compute Integer
allocateVar = do
    ret <- fmap varCounter get
    modify $ \st -> st { varCounter = ret + 1 }
    return ret


instantiateLam :: Type -> Compute Type
instantiateLam (TInf v t cons) = do
    newvar <- allocateVar
    let subst = Map.singleton (TVar v) (TVar newvar)
    mapM_ (addEquation "inf constr" . substituteEquation subst) cons
    return $ substituteType subst t
instantiateLam (TSup v t cons) = do
    newvar <- allocateVar
    let subst = Map.singleton (TVar v) (TVar newvar)
    mapM_ (addEquation "sup constr" . substituteEquation subst) cons
    return $ substituteType subst t
instantiateLam _ = error "Tried to lambda-instantiate a non-lambda"

twoColumn :: Int -> String -> String -> String
twoColumn width cola colb 
    = cola ++ replicate spaces ' ' ++ colb
    where
    spaces = if length cola + 4 < width
                 then width - length cola
                 else 4

addEquation :: String -> Equation -> Compute ()
addEquation reason eq@(a :< b) = do
    st <- get
    if eq `Set.member` seenSet st
        then return ()
        else do
            depth <- ask
            liftIO $ putStrLn (twoColumn 50 (concat (replicate depth "  ") ++ show eq) ("(" ++ reason ++ ")"))
            st <- get
            put (st { seenSet = Set.insert eq (seenSet st) })
            local (+1) $ (transformEquation eq >> performElimination eq)
    
isLim :: Type -> Bool
isLim (TVar {}) = True
isLim (TInf {}) = True
isLim (TSup {}) = True
isLim _ = False

transformEquation :: Equation -> Compute ()
transformEquation (TArrow a b :< TArrow a' b') = do
    addEquation "arrow" (a' :< a)
    addEquation "arrow" (b :< b')
    
transformEquation (TTuple a b :< TTuple a' b') = do
    addEquation "tuple" (a :< a')
    addEquation "tuple" (b :< b')

transformEquation (sub@(TInf {}) :< sup) | not (isLim sup) = do
    sub' <- instantiateLam sub
    addEquation "instantiate" (sub' :< sup)

transformEquation (sub :< sup@(TSup {})) | not (isLim sub) = do
    sup' <- instantiateLam sup
    addEquation "instantiate" (sub :< sup')

transformEquation _ = return ()

performElimination :: Equation -> Compute ()
performElimination (sub :< sup) = do
    st <- get
    
    forEach (seenSet st) $ \eq -> 
                case eq of
                    x :< y | y == sub
                        -> addEquation ("left-elim  " ++ show sub) (x :< sup)
                    _   -> return ()
    
    forEach (seenSet st) $ \eq ->
                case eq of
                    x :< y | x == sup
                        -> addEquation ("right-elim " ++ show sup) (sub :< y)
                    _   -> return ()

freeVars :: Set.Set Type -> Type -> Set.Set Type
freeVars env (TAtom x) = Set.empty
freeVars env (TArrow a b) = freeVars env a `Set.union` freeVars env b
freeVars env (TTuple a b) = freeVars env a `Set.union` freeVars env b
freeVars env (TVar a) = if TVar a `Set.member` env 
                            then Set.empty 
                            else Set.singleton (TVar a)
freeVars env (TInf v t cons) 
    = freeVars xenv t `Set.union` foldr (Set.union . eqFreeVars) Set.empty cons
    where 
    xenv = Set.insert (TVar v) env
    eqFreeVars (a :< b) = freeVars xenv a `Set.union` freeVars xenv b
freeVars env (TSup v t cons) 
    = freeVars xenv t `Set.union` foldr (Set.union . eqFreeVars) Set.empty cons
    where 
    xenv = Set.insert (TVar v) env
    eqFreeVars (a :< b) = freeVars xenv a `Set.union` freeVars xenv b

assert :: (MonadPlus m) => Bool -> a -> m a
assert cond val = if cond then return val else mzero

same :: (Eq a, MonadPlus m) => a -> [a] -> m a
same def [x] = return x
same def (x:xs) = same def xs >>= \s -> assert (s == x) s
same def []  = return def  -- not recursive, only special case

lowerBounds :: [Equation] -> Set.Set Type -> Type -> [Type]
lowerBounds eqs env t = mapMaybe (\(a :< b) -> assert (b == t) a)
                      $ eqs

upperBounds :: [Equation] -> Set.Set Type -> Type -> [Type]
upperBounds eqs env t = mapMaybe (\(a :< b) -> assert (a == t) b)
                      $ eqs

gen2Helper :: (Type -> Type -> Type)
           -> (Type, Type)
           -> ([Equation] -> Set.Set Type -> Type -> Type)
           -> ([Equation] -> Set.Set Type -> Type -> Type)
           -> (Integer -> Type -> [Equation] -> Type)
           -> [Equation] -> Set.Set Type
           -> Type
gen2Helper tcons (a,b) genArg1 genArg2 genCons eqs env = 
    Set.fold eliminate base (freeVars env base)
    where
    shared = freeVars env a `Set.intersection` freeVars env b
    base = tcons (genArg1 eqs shared a) (genArg2 eqs shared b)
    eliminate v t = genCons (name v) t
                            (prune (env `Set.union` freeVars env t) eqs)
    name (TVar v) = v

generalizeInf :: [Equation] -> Set.Set Type -> Type -> Type
generalizeInf eqs env (TAtom x) = TAtom x
generalizeInf eqs env (TArrow a b) = 
    gen2Helper TArrow (a,b) generalizeSup generalizeInf TInf eqs env
generalizeInf eqs env (TTuple a b) = 
    gen2Helper TTuple (a,b) generalizeInf generalizeInf TInf eqs env
generalizeInf eqs env var@(TVar {}) = 
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeInf eqs env) 
                           $ lowerBounds eqs env var
generalizeInf eqs env l@(TInf {}) = l  -- ahh, simple
generalizeInf eqs env l@(TSup {}) = l

generalizeSup :: [Equation] -> Set.Set Type -> Type -> Type
generalizeSup eqs env (TAtom x) = TAtom x
generalizeSup eqs env (TArrow a b) = 
    gen2Helper TArrow (a,b) generalizeInf generalizeSup TSup eqs env
generalizeSup eqs env (TTuple a b) =
    gen2Helper TTuple (a,b) generalizeSup generalizeSup TSup eqs env
generalizeSup eqs env var@(TVar {}) =
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeSup eqs env)
                           $ upperBounds eqs env var
generalizeSup eqs env l@(TInf {}) = l
generalizeSup eqs env l@(TSup {}) = l


compute :: [Equation] -> Compute ()
compute eqs = do
    mapM_ (addEquation "init") eqs

reduce :: Integer -> [Equation] -> IO [Equation]
reduce start eqs = fmap (Set.toList . seenSet) 
                 $ flip runReaderT 0
                 $ execStateT (compute eqs)
                 $ ComputeState { varCounter    = start
                                , seenSet       = Set.empty
                                }

prune :: Set.Set Type -> [Equation] -> [Equation]
prune ts = filter $ \ (a :< b) -> all isInteresting [a,b]
    where
    isInteresting :: Type -> Bool
    isInteresting (TAtom _) = True
    isInteresting x = x `Set.member` ts

main :: IO ()
main = do
    reduced <- reduce 100 eqs
    putStrLn ""
    putStrLn "-- CONCLUSIONS --"
    putStrLn ""
    mapM_ print $ prune (Set.fromList [TVar 1, TVar 2]) reduced
    putStrLn ""
    print (generalizeInf reduced Set.empty (TVar 0))
    where
    eqs = [ TVar 4                            :< TArrow (TVar 0) (TVar 3)
          , TArrow (TVar 7) (TVar 7)          :< TVar 0
          , TTuple (TVar 1) (TVar 2)          :< TVar 3
          , TVar 0                            :< TArrow (TVar 5) (TVar 1)
          , TAtom "Int"                       :< TVar 5
          , TVar 0                            :< TArrow (TVar 6) (TVar 2)
          , TAtom "Str"                       :< TVar 6
          ]
    
    {-
    eqs = [ TVar 4                            :< TArrow (TVar 0) (TVar 3)
          , TLam 0 (TArrow (TVar 0) (TVar 0)) [] :< TVar 0
          , TTuple (TVar 1) (TVar 2)          :< TVar 3
          , TVar 0                            :< TArrow (TVar 5) (TVar 1)
          , TAtom "Int"                       :< TVar 5
          , TVar 0                            :< TArrow (TVar 6) (TVar 2)
          , TAtom "Str"                       :< TVar 6
          ]
    -}
