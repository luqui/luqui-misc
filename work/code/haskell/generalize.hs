{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace

{---------------------
 - GENERAL UTILITIES -
 ---------------------}

peek :: (Show a) => a -> a
peek x = trace (show x) x


twoColumn :: Int -> String -> String -> String
twoColumn width cola colb 
    = cola ++ replicate spaces ' ' ++ colb
    where
    spaces = if length cola + 4 < width
                 then width - length cola
                 else 4


forEach :: (Monad m, Ord a) => Set.Set a -> (a -> m ()) -> m ()
forEach set action = Set.fold (\item m -> m >> action item) (return ()) set


assert :: (MonadPlus m) => Bool -> a -> m a
assert cond val = if cond then return val else mzero


same :: (Eq a, MonadPlus m) => a -> [a] -> m a
same def [x] = return x
same def (x:xs) = same def xs >>= \s -> assert (s == x) s
same def []  = return def  -- not recursive, only special case


{-------------------
 - DATA STRUCTURES -
 -------------------}

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


data Context 
    = InfContext
    | SupContext
    deriving (Eq,Show)

swapContext :: Context -> Context
swapContext InfContext = SupContext
swapContext SupContext = InfContext



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




{-------------------
 -REDUCTION ENGINE -
 -------------------}

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


reduce :: Integer -> [Equation] -> IO [Equation]
reduce start eqs = fmap (Set.toList . seenSet) 
                 $ flip runReaderT 0
                 $ execStateT (mapM_ (addEquation "init") eqs)
                 $ ComputeState { varCounter    = start
                                , seenSet       = Set.empty
                                }

{-------------------------
 - GENERALIZATION ENGINE -
 -------------------------}


freeVarsEq :: Set.Set Type -> Equation -> Set.Set Type
freeVarsEq env (a :< b) = freeVars env a `Set.union` freeVars env b


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



lowerBounds :: [Equation] -> Set.Set Type -> Type -> [Type]
lowerBounds eqs env t = mapMaybe (\(a :< b) -> assert (b == t) a)
                      $ eqs

upperBounds :: [Equation] -> Set.Set Type -> Type -> [Type]
upperBounds eqs env t = mapMaybe (\(a :< b) -> assert (a == t) b)
                      $ eqs


{--------------------------}


main :: IO ()
main = do
    reduce 100 eqs >> return ()
    where
    eqs = [ TVar 0 :< TArrow (TVar 1) (TVar 2)
          , TVar 3 :< TVar 1
          , TVar 2 :< TArrow (TVar 4) (TVar 5)
          , TAtom "Int" :< TVar 4
          , TArrow (TVar 3) (TVar 5) :< TVar 6
          , TAtom "Int" :< TAtom "Num"
          , TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))) [ TVar 0 :< TAtom "Num" ] :< TVar 0
          ]
