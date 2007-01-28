{-# OPTIONS_GHC -fglasgow-exts -fimplicit-params #-}

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


fixedPoint :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixedPoint cmp mod init = 
    let next = mod init in
        if cmp init next
            then next
            else fixedPoint cmp mod next


{-------------------
 - DATA STRUCTURES -
 -------------------}

data Type where
    TAtom  :: String             -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type       -> Type  -- functions
    TTuple :: Type -> Type       -> Type  -- tuples
    TVar   :: Integer            -> Type  -- type variable
    TInf   :: Integer -> Type -> Set.Set Equation -> Type  -- universal type
    TSup   :: Integer -> Type -> Set.Set Equation -> Type  -- existential type
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar v)     = show v
    show (TInf i t cons)   = "^" ++ show i ++ " " ++ show t ++ " " ++ show (Set.toList cons)
    show (TSup i t cons)   = "v" ++ show i ++ " " ++ show t ++ " " ++ show (Set.toList cons)

name :: Type -> Integer
name (TVar x) = x
name _ = error "That type has no name"

type Subst = Map.Map Type Type
type SubstID = Integer
type Constraint = (Set.Set Type, Set.Set Type)

data Equation where
    (:<) :: Type -> Type -> Equation
    deriving (Eq,Ord)

instance Show Equation where
    show (a :< b) = show a ++ " <: " ++ show b


data Context where
    InfContext :: Context
    SupContext :: Context
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
    = TInf v (substituteType subst t) (Set.map (substituteEquation subst) cons)
    where
    subst = Map.delete (TVar v) sub
substituteType sub (TSup v t cons) 
    = TSup v (substituteType subst t) (Set.map (substituteEquation subst) cons)
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
    forEach cons $ addEquation "inf constr" . substituteEquation subst
    return $ substituteType subst t
instantiateLam (TSup v t cons) = do
    newvar <- allocateVar
    let subst = Map.singleton (TVar v) (TVar newvar)
    forEach cons $ addEquation "sup constr" . substituteEquation subst
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


freeVarsEq :: (?env :: Set.Set Type) => Equation -> Set.Set Type
freeVarsEq (a :< b) = freeVars a `Set.union` freeVars b


freeVars :: (?env :: Set.Set Type) => Type -> Set.Set Type
freeVars (TAtom x) = Set.empty
freeVars (TArrow a b) = freeVars a `Set.union` freeVars b
freeVars (TTuple a b) = freeVars a `Set.union` freeVars b
freeVars (TVar a) = if TVar a `Set.member` ?env
                            then Set.empty 
                            else Set.singleton (TVar a)
freeVars (TInf v t cons) 
    = let ?env = Set.insert (TVar v) ?env in
      freeVars t `Set.union` Set.fold (Set.union . freeVarsEq) Set.empty cons
freeVars (TSup v t cons) 
    = let ?env = Set.insert (TVar v) ?env in
      freeVars t `Set.union` Set.fold (Set.union . freeVarsEq) Set.empty cons


-- XXX badly implemented
lowerBounds :: Set.Set Equation -> Type -> Set.Set Type
lowerBounds eqs t = Set.fromList $ mapMaybe (\(a :< b) -> assert (b == t) a) $ Set.toList eqs

upperBounds :: Set.Set Equation -> Type -> Set.Set Type
upperBounds eqs t = Set.fromList $ mapMaybe (\(a :< b) -> assert (a == t) b) $ Set.toList eqs


subtype :: (?eqs :: Set.Set Equation) => Type -> Type -> Bool
subtype (TArrow t u) (TArrow t' u') = subtype t' t && subtype u u'
subtype (TTuple t u) (TTuple t' u') = subtype t t' && subtype u u'
-- XXX should unify for sup and inf types?
subtype  a b = a == b || (a :< b) `Set.member` ?eqs


minimalAdd :: (?eqs :: Set.Set Equation) => Type -> Set.Set Type -> Set.Set Type
minimalAdd t set = 
    let filtered = Set.filter (not . (t `subtype`)) set in
        if Set.fold (\a b -> b || a `subtype` t) False filtered
            then filtered
            else Set.insert t filtered

maximalAdd :: (?eqs :: Set.Set Equation) => Type -> Set.Set Type -> Set.Set Type
maximalAdd t set = 
    let filtered = Set.filter (not . (`subtype` t)) set in
        if Set.fold (\a b -> b || t `subtype` a) False filtered
            then filtered
            else Set.insert t filtered


reduceConstraint :: (?eqs :: Set.Set Equation) => Constraint -> Constraint
reduceConstraint (lower,upper) =
    (Set.fold maximalAdd Set.empty lower, Set.fold minimalAdd Set.empty upper)

getSingleton :: Set.Set a -> a
getSingleton = Set.fold const undefined

constraintToSubst :: Constraint -> Maybe Type
constraintToSubst (lower,upper)
    | Set.size lower == 0 && Set.size upper == 1  
        = Just $ getSingleton upper
    | Set.size lower == 1 && Set.size upper == 0
        = Just $ getSingleton lower
    | Set.size lower == 1 && Set.size upper == 1 && getSingleton lower == getSingleton upper
        = Just $ getSingleton lower
    | otherwise = Nothing

substituteConstraint :: Subst -> Constraint -> Constraint
substituteConstraint sub (lower,upper) = 
    (Set.map (substituteType sub) lower, Set.map (substituteType sub) upper)

constraintsToSubst1 :: (?eqs :: Set.Set Equation) 
                    => (Map.Map Type Constraint, Subst) -> (Map.Map Type Constraint, Subst)
constraintsToSubst1 (cons, sub) = 
    let cons' = Map.mapWithKey (\k -> reduceConstraint . filterSelf k . substituteConstraint sub) cons
        sub'  = Map.map fromJust . Map.filter isJust . Map.map constraintToSubst $ cons'
    in
    (cons' Map.\\ sub', mapSub (sub `Map.union` sub'))
    where
    mapSub s = Map.map (substituteType s) s
    filterSelf x (a,b) = (Set.filter (/= x) a, Set.filter (/= x) b)

constraintsToSubst :: (?eqs :: Set.Set Equation) 
                   => Map.Map Type Constraint -> (Map.Map Type Constraint, Subst)
constraintsToSubst cons = 
    fixedPoint (==) constraintsToSubst1 (cons, Map.empty)

findConstraints :: (?env :: Set.Set Type) => Set.Set Equation -> Map.Map Type Constraint
findConstraints eqs =
    Set.fold insertConstraint Map.empty eqs
    where
    insertConstraint t =
        let insa = case t of 
                       a@(TVar _) :< b 
                         | not (a `Set.member` ?env) -> 
                            -- add b as an upper bound to a
                            Map.insertWith consUnion a (Set.empty, Set.singleton b)
                       _ -> id
            insb = case t of
                       a :< b@(TVar _)
                         | not (b `Set.member` ?env) -> 
                            -- add a as a lower bound to b
                            Map.insertWith consUnion b (Set.singleton a, Set.empty)
                       _ -> id
        in insb . insa
    consUnion (lower,upper) (lower',upper') =
        (lower `Set.union` lower', upper `Set.union` upper')

generalizeInf :: (?env :: Set.Set Type) 
              => (Map.Map Type Constraint, Subst) -> Type -> Type
generalizeInf (cons,subst) t = 
    snd $ fixedPoint (==) (genOverFree . peek) $ (Set.empty, substituteType subst t)
    where
    genOverFree :: (Set.Set Type, Type) -> (Set.Set Type, Type)
    genOverFree (vs,t) = Set.fold genOver (vs,t) $ freeVars t
   
    genOver :: Type -> (Set.Set Type, Type) -> (Set.Set Type, Type)
    genOver v (vs,t) = 
        let (lower, upper) = Map.findWithDefault (Set.empty, Set.empty) v cons in
        ( Set.insert v vs
        , TInf (name v) t 
            $ Set.filter (\(a :< b) -> not (a `Set.member` vs || b `Set.member` vs))
            $ Set.map (:< v) lower `Set.union` Set.map (v :<) upper
        )
        


{--------------------------}


main :: IO ()
main = do
    reduced <- reduce 100 eqs
    let ?eqs = Set.fromList reduced
        ?env = Set.empty
    let (cons, subst) = constraintsToSubst $ findConstraints ?eqs
    putStrLn "----------"
    putStrLn ""
    printMap subst
    putStrLn ""
    printMap cons
    putStrLn ""
    putStrLn "----------"
    print $ generalizeInf (cons, subst) (TVar 6)

    where
    
    printMap :: (Ord k, Show k, Show v) => Map.Map k v -> IO ()
    printMap = Map.foldWithKey (\k v m -> m >> showPair k v) (return ())
    
    showPair k v = putStrLn $ "  " ++ show k ++ " => " ++ show v

    eqs = [ TVar 0 :< TArrow (TVar 1) (TVar 2)
          , TVar 3 :< TVar 1
          , TVar 2 :< TArrow (TVar 4) (TVar 5)
          , TAtom "Int" :< TVar 4
          , TArrow (TVar 3) (TVar 5) :< TVar 6
          , TAtom "Int" :< TAtom "Num"
          , TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))) (Set.singleton (TVar 0 :< TAtom "Num")) :< TVar 0
          ]
