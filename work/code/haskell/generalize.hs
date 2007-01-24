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
    TVar   :: Integer            -> Type  -- singular type
    TLim   :: Integer            -> Type  -- limit type
    TLam   :: Integer -> Type -> [Equation] -> Type  -- universal type
    deriving (Eq,Ord)

-- Note that a TLam is just an infimum type.  For example, \x (x -> x)
-- (the type of the identity) is a subtype of Int -> Int, Str -> Str,
-- and every other type that looks like a -> a.  So it's just the
-- greatest lower bound of all those types.  We need it so we can
-- specify universal types by their defining sets (keep in mind
-- that the defining sets we can specify are very limited--certainly
-- much less than those of first-order logic--which is why we have
-- a hope of this algorithm still being decidable).

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar v)     = show v
    show (TLim v)     = "L" ++ show v
    show (TLam i t cons)   = "\\" ++ show i ++ " " ++ show t ++ " " ++ show cons

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
substituteType sub (TLam v t cons) 
    = TLam v (substituteType subst t) (map (substituteEquation subst) cons)
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
instantiateLam (TLam v t cons) = do
    newvar <- allocateVar
    let subst = Map.singleton (TVar v) (TVar newvar)
    mapM_ (addEquation "inst constr" . substituteEquation subst) cons
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
isLim (TLim {}) = True
isLim (TLam {}) = True
isLim _ = False

transformEquation :: Equation -> Compute ()
transformEquation (TArrow a b :< TArrow a' b') = do
    addEquation "arrow" (a' :< a)
    addEquation "arrow" (b :< b')
    
transformEquation (TTuple a b :< TTuple a' b') = do
    addEquation "tuple" (a :< a')
    addEquation "tuple" (b :< b')

transformEquation (sub@(TLam {}) :< sup) | not (isLim sup) = do
    sub' <- instantiateLam sub
    addEquation "instantiate" (sub' :< sup)

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
freeVars env (TLim a) = if TLim a `Set.member` env
                            then Set.empty
                            else Set.singleton (TLim a)
freeVars env (TLam v t cons) 
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

generalizeInf :: [Equation] -> Set.Set Type -> Type -> Type
generalizeInf eqs env (TAtom x) = TAtom x
generalizeInf eqs env (TArrow a b) = 
    Set.fold eliminate arr (freeVars env arr)
    where
    shared = freeVars env a `Set.intersection` freeVars env b
    arr = TArrow (generalizeSup eqs shared a) (generalizeInf eqs shared b)
    eliminate v t = TLam (name v) (substituteType (subst v) t) 
                         (map (substituteEquation (subst v))
                           $ prune (env `Set.union` freeVars env t) eqs)
    subst v = Map.singleton v (rename v)
    name (TVar v) = v
    name (TLim v) = v
    name _ = error "complex types have no names"
    rename = TVar . name
generalizeInf eqs env (TTuple {}) = error "fuck that"
generalizeInf eqs env var@(TVar {}) = 
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeInf eqs env) 
                           $ lowerBounds eqs env var
generalizeInf eqs env var@(TLim {}) = 
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeInf eqs env)
                           $ lowerBounds eqs env var
generalizeInf eqs env l@(TLam {}) = l  -- ahh, simple

generalizeSup :: [Equation] -> Set.Set Type -> Type -> Type
generalizeSup eqs env (TAtom x) = TAtom x
generalizeSup eqs env (TArrow a b) = 
    if Set.null (freeVars env arr) then arr else TAtom "Top" -- loss of info!
    where
    shared = freeVars env a `Set.intersection` freeVars env b
    arr = TArrow (generalizeInf eqs shared a) (generalizeSup eqs shared b)
generalizeSup eqs env (TTuple {}) = error "not handling tuples"
generalizeSup eqs env var@(TVar {}) =
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeSup eqs env)
                           $ upperBounds eqs env var
generalizeSup eqs env var@(TLim {}) = 
    if var `Set.member` env
        then var
        else fromMaybe var $ same (TAtom "Top") 
                           $ map (generalizeSup eqs env)
                           $ upperBounds eqs env var
generalizeSup eqs env l@(TLam {}) = l


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
    mapM_ print $ prune (Set.fromList [TLim 1, TLim 2]) reduced
    putStrLn ""
    print (generalizeInf reduced Set.empty (TLim 0))
    where
    eqs = [ TLim 4                            :< TArrow (TLim 0) (TLim 3)
          , TArrow (TLim 7) (TLim 7)          :< TLim 0
          , TTuple (TLim 1) (TLim 2)          :< TLim 3
          , TLim 0                            :< TArrow (TLim 5) (TLim 1)
          , TAtom "Int"                       :< TLim 5
          , TLim 0                            :< TArrow (TLim 6) (TLim 2)
          , TAtom "Str"                       :< TLim 6
          ]

    {-
    eqs = [ TLim 4                            :< TArrow (TLim 0) (TLim 3)
          , TLam 0 (TArrow (TVar 0) (TVar 0)) :< TLim 0
          , TTuple (TLim 1) (TLim 2)          :< TLim 3
          , TLim 0                            :< TArrow (TLim 5) (TLim 1)
          , TAtom "Int"                       :< TLim 5
          , TLim 0                            :< TArrow (TLim 6) (TLim 2)
          , TAtom "Str"                       :< TLim 6
          ]
    -}
