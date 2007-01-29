{-# OPTIONS_GHC -fglasgow-exts -fimplicit-params #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace
import Data.List (intersperse)

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
    TAtom  :: String -> [Type]   -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type       -> Type  -- functions
    TTuple :: Type -> Type       -> Type  -- tuples
    TVar   :: Integer            -> Type  -- type variable
    TInf   :: Integer -> Type -> Set.Set Equation -> Type  -- universal type
    TSup   :: Integer -> Type -> Set.Set Equation -> Type  -- existential type
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom a ts) = 
        if null ts 
            then a 
            else "(" ++ a ++ " " ++ concat (intersperse " " (map show ts)) ++ ")"
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar v)     = show v
    show (TInf i t cons)   = "^" ++ show i ++ " " ++ show t ++ " " ++ show (Set.toList cons)
    show (TSup i t cons)   = "v" ++ show i ++ " " ++ show t ++ " " ++ show (Set.toList cons)

-- for occurs check
exclusive :: Type -> Type -> Bool
exclusive (TAtom {}) (TArrow {})  = True
exclusive (TAtom {}) (TTuple {})  = True
exclusive (TArrow {}) (TAtom {})  = True
exclusive (TArrow {}) (TTuple {}) = True
exclusive (TTuple {}) (TAtom {})  = True
exclusive (TTuple {}) (TArrow {}) = True
exclusive _           _           = False

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

contextToCons :: Context -> Integer -> Type -> Set.Set Equation -> Type
contextToCons InfContext = TInf
contextToCons SupContext = TSup


substituteType :: Subst -> Type -> Type
substituteType sub x
    | x `Map.member` sub = sub Map.! x
substituteType sub (TAtom n ts) = TAtom n $ map (substituteType sub) ts
substituteType sub (TArrow a b) 
    = TArrow (substituteType sub a) (substituteType sub b)
substituteType sub (TTuple a b) 
    = TTuple (substituteType sub a) (substituteType sub b)
substituteType sub (TVar a) = TVar a
substituteType sub (TInf v t cons) 
    = TInf v (substituteType subst t) (Set.map (substituteEquation subst) cons)
    where
    subst = Map.delete (TVar v) sub
substituteType sub (TSup v t cons) 
    = TSup v (substituteType subst t) (Set.map (substituteEquation subst) cons)
    where
    subst = Map.delete (TVar v) sub


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


instantiateLam :: (?env :: Set.Set Type) => Type -> Compute Type
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



addEquation :: (?env :: Set.Set Type) => String -> Equation -> Compute ()
addEquation reason eq@(a :< b) = do
    st <- get
    if eq `Set.member` seenSet st
        then return ()
        else do
            depth <- ask
            liftIO $ putStrLn (twoColumn 50 (concat (replicate depth "  ") ++ show eq) ("(" ++ reason ++ ")"))
            st <- get
            put (st { seenSet = Set.insert eq (seenSet st) })
            local (+1) $ (checkEquation eq >> transformEquation eq >> performElimination eq)

    
isLim :: Type -> Bool
isLim (TVar {}) = True
isLim (TInf {}) = True
isLim (TSup {}) = True
isLim _ = False


checkEquation :: (?env :: Set.Set Type) => Equation -> Compute ()
checkEquation (a :< b) = do
    when (exclusive a b) ocheck
    case (a,b) of
        (TVar _, TVar _) -> return ()
        (TVar t', u) 
            | TVar t' `Set.member` nonAtomFree u -> ocheck
        (t, TVar u')
            | TVar u' `Set.member` nonAtomFree t -> ocheck
        _ -> return ()
    where
    ocheck = fail $ "Occurs check: " ++ show (a :< b)
    
    nonAtomFree a@(TAtom {}) = Set.empty
    nonAtomFree x = freeVars x


transformEquation :: (?env :: Set.Set Type) => Equation -> Compute ()
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


performElimination :: (?env :: Set.Set Type) => Equation -> Compute ()
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


reduce :: (?env :: Set.Set Type) => Integer -> [Equation] -> IO [Equation]
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
freeVars (TAtom x ts) = Set.unions $ map freeVars ts
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
    let (l', u') = (Set.fold maximalAdd Set.empty lower, Set.fold minimalAdd Set.empty upper)
        inter    = l' `Set.intersection` u'
    in
    if Set.size inter > 0
        then (inter,inter)
        else (l', u')

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
    Map.foldWithKey (\k v (cons, sub) ->
        case constraintToSubst . reduceConstraint . filterSelf k . substituteConstraint sub $ v of
            Just t  -> let newmap = mapSub (Map.insert k t sub)
                          in (Map.map (substituteConstraint newmap) (Map.delete k cons), newmap)
            Nothing -> (cons, sub)
    ) (cons,sub) cons
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

generalize :: (?env :: Set.Set Type, ?eqs :: Set.Set Equation)
           => Context -> (Map.Map Type Constraint, Subst) -> Type -> Type
generalize cxt (cons,subst) t = 
    fixedPoint (==) genOverFree $ substituteType subst t
    where
    genOverFree :: Type -> Type
    genOverFree t = Set.fold genOver t $ freeVars t
   
    genOver :: Type -> Type -> Type
    genOver v t = 
        let myCons = fromMaybe (Set.empty, Set.empty) $ Map.lookup v cons
            lowerEqs = Set.map (:< v) . Set.filter (/= v) $ fst myCons
            upperEqs = Set.map (v :<) . Set.filter (/= v) $ snd myCons
            allEqs = lowerEqs `Set.union` upperEqs
        in
        contextToCons cxt (name v) t allEqs

{--------------------------}


main :: IO ()
main = do
    let ?env = Set.empty
    reduced <- reduce 100 eqs
    let ?eqs = Set.fromList reduced
    let (cons, subst) = constraintsToSubst $ findConstraints ?eqs
    putStrLn "----------"
    putStrLn ""
    printMap subst
    putStrLn ""
    printMap cons
    putStrLn ""
    putStrLn "----------"
    print $ generalize InfContext (cons,subst) (TVar 20)

    where
    
    printMap :: (Ord k, Show k, Show v) => Map.Map k v -> IO ()
    printMap = Map.foldWithKey (\k v m -> m >> showPair k v) (return ())
    
    showPair k v = putStrLn $ "  " ++ show k ++ " => " ++ show v

    o = Set.empty

    -- The type that is currently inferred for the following is not quite right:
    -- It says ^101 ^10 (10 -> 10) [ 10 <: Ref Int, 10 <: Ref 101] [ Int <: 101, 101 <: Num].
    -- This is pretty damn close, but unfortunately, 10 <: Ref Int is deadly.  The
    -- function below would work on Ref Num, but unfortunately the type would forbid this.
    -- (esp. noting the law that Ref x <: Ref y implies x = y)
    
    {- fix \f x { x := !x + 1; if 10 < !x then x else f x } -}
    eqs = [ TInf 0 (TArrow (TVar 0) (TAtom "Ref" [TVar 0])) o :< tMkRef
          , TInf 0 (TArrow (TAtom "Ref" [TVar 0]) (TVar 0)) o :< tReadRef
          , TInf 0 (TArrow (TVar 0) (TArrow (TAtom "Ref" [TVar 0]) (TAtom "Unit" []))) o :< tWriteRef
          , TArrow (TAtom "Unit" []) (TInf 0 (TArrow (TVar 0) (TVar 0)) o) :< tSeq
          , TInf 0 (TArrow (TArrow (TVar 0) (TVar 0)) (TVar 0)) o :< tFix
          , TArrow (TAtom "Bool" []) (TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))) o) :< tIf
          , TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))) (Set.singleton (TVar 0 :< TAtom "Num" [])) :< tPlus
          , TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TAtom "Bool" []))) o :< tLess
          , TAtom "Int" [] :< TAtom "Num" []
          
          -- f                     :: 16
          -- x                     :: 10
          -- !x                    :: 11
          , tReadRef :< TArrow (TVar 10) (TVar 11)
          -- !x + 1                :: 12
          , tPlus :< TArrow (TVar 11) (TArrow (TAtom "Int" []) (TVar 12))
          -- x := !x + 1           :: 13
          , tWriteRef :< TArrow (TVar 12) (TArrow (TVar 10) (TVar 13))
          
          -- !x                    :: 14
          , tReadRef :< TArrow (TVar 10) (TVar 14)
          -- 10 < !x               :: 15
          , tLess :< TArrow (TAtom "Int" []) (TArrow (TVar 14) (TVar 15))
          -- f x                   :: 17
          , TVar 16 :< TArrow (TVar 10) (TVar 17)
          -- if 10 < !x then x else f x :: 18
          , tIf :< TArrow (TVar 15) (TArrow (TVar 10) (TArrow (TVar 17) (TVar 18)))

          -- x := !x + 1; if ...   :: 19
          , tSeq :< TArrow (TVar 13) (TArrow (TVar 18) (TVar 19))

          -- fix \f x {...}        :: 20
          , tFix :< TArrow (TArrow (TVar 16) (TArrow (TVar 10) (TVar 19))) (TVar 20)
          ]

    tMkRef    = TVar 0
    tReadRef  = TVar 1
    tWriteRef = TVar 2
    tSeq      = TVar 3
    tIf       = TVar 4
    tPlus     = TVar 5
    tLess     = TVar 6
    tFix      = TVar 7

    {-
    eqs = [ TVar 0 :< TArrow (TVar 1) (TVar 2)
          , TVar 3 :< TVar 1
          , TVar 2 :< TArrow (TVar 4) (TVar 5)
          , TAtom "Int" [] :< TVar 4
          , TArrow (TVar 3) (TVar 5) :< TVar 6
          , TAtom "Int" [] :< TAtom "Num" []
          , TInf 0 (TArrow (TVar 0) (TArrow (TVar 0) (TVar 0))) (Set.singleton (TVar 0 :< TAtom "Num" [])) :< TVar 0
          ]
    -}
