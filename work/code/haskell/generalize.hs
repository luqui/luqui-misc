{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State

data Type where
    TAtom  :: String          -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type    -> Type  -- functions
    TVar   :: Integer         -> Type  -- existential variables
    TGen   :: Integer         -> Type  -- generalized variables
    TLam   :: Integer -> Type -> Type  -- universal types
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TVar   v)   = "v" ++ show v
    show (TGen   g)   = "G" ++ show g
    show (TLam i t)   = "\\v" ++ show i ++ " " ++ show t

type Subst = Map.Map Type Type
type SubstID = Integer

data Equation where
    Equation :: Maybe SubstID -> Type -> Type -> Equation
    deriving (Eq,Ord)

instance Show Equation where
    show (Equation _ a b) = show a ++ " <: " ++ show b


substituteType :: Subst -> Type -> Type
substituteType sub x
    | x `Map.member` sub = sub Map.! x
substituteType sub (TArrow a b) 
    = TArrow (substituteType sub a) (substituteType sub b)
substituteType sub (TLam v t) 
    = TLam v (substituteType (Map.delete (TVar v) sub) t)
substituteType _ x = x


forEach :: (Monad m, Ord a) => Set.Set a -> (a -> m ()) -> m ()
forEach set action = Set.fold (\item m -> m >> action item) (return ()) set


data ComputeState where
    ComputeState 
        { varCounter    :: Integer
        , seenSet       :: Set.Set Equation
        , substitutions :: Map.Map SubstID Subst
        } :: ComputeState

type Compute a = StateT ComputeState IO a

allocateVar :: Compute Integer
allocateVar = do
    ret <- fmap varCounter get
    modify $ \st -> st { varCounter = ret + 1 }
    return ret

getSubst :: SubstID -> Compute Subst
getSubst substid = do
    fmap (Map.findWithDefault Map.empty substid . substitutions) get

insertSubst :: SubstID -> Type -> Type -> Compute ()
insertSubst substid k v = do
    subst <- getSubst substid
    modify $ \st -> st { substitutions = 
                  Map.insert (substid) (Map.insert k v subst) (substitutions st) }

instantiateGen :: SubstID -> Type -> Compute Type
instantiateGen substid (TGen g) = do
    subst <- getSubst substid
    if TGen g `Map.member` subst
        then return $ subst Map.! TGen g
        else do
            newvar <- allocateVar
            insertSubst substid (TGen g) (TVar newvar)
            return $ TVar newvar
instantiateGen substid (TArrow a b) = do
    a' <- instantiateGen substid a
    b' <- instantiateGen substid b
    return $ TArrow a b
instantiateGen substid (TLam v t) = do
    -- this is safe because you can't lambda over a Gen
    t' <- instantiateGen substid t
    return $ TLam v t' 

instantiateLam :: Type -> Compute Type
instantiateLam (TLam v t) = do
    newvar <- allocateVar
    return $ substituteType (Map.singleton (TVar v) (TVar newvar)) t
instantiateLam _ = error "Tried to lambda-instantiate a non-lambda"

generalizeLam :: Type -> Compute Type
generalizeLam (TLam v t) = do
    newvar <- allocateVar
    return $ substituteType (Map.singleton (TVar v) (TGen newvar)) t
generalizeLam _ = error "Tried to lambda-generalize a non-lambda"


addEquation :: Equation -> Compute ()
addEquation eq@(Equation substid a b) = do
    toAdd <- if isJust substid
                then do
                    a' <- instantiateGen (fromJust substid) a
                    b' <- instantiateGen (fromJust substid) b
                    return $ Equation substid a' b'
                else return eq
                
    st <- get
    if eq `Set.member` seenSet st
        then return ()
        else do
            transformEquation toAdd
            put (st { seenSet = Set.insert toAdd (seenSet st) })

substCombine :: Maybe SubstID -> Maybe SubstID -> Maybe SubstID
substCombine Nothing Nothing = Nothing
substCombine Nothing (Just a) = Just a
substCombine (Just a) Nothing = Just a
substcombine (Just a) (Just b) 
    | a == b    = Just a
    | otherwise = error "Attempt to combine two substitution ids (I don't know what to do yet)"

transformEquation :: Equation -> Compute ()
transformEquation (Equation subst (TArrow a b) (TArrow a' b')) = do
    addEquation (Equation subst a' a)
    addEquation (Equation subst b b')
transformEquation (Equation subst sub@(TLam v t) sup) = do
    sub' <- instantiateLam sub
    addEquation (Equation subst sub' sup)
transformEquation (Equation subst sub sup@(TLam v t)) = do
    sup' <- generalizeLam sup
    addEquation (Equation subst sub sup')
transformEquation (Equation subst sub sup) = do
    st <- get
    
    case sub of
        TVar a' -> forEach (seenSet st) $ \eq -> 
                        case eq of
                            Equation subst' x (TVar y') | y' == a'
                                -> addEquation (Equation (substCombine subst subst') x sup)
                            _   -> return ()
        _ -> return ()
    
    case sup of
        TVar b' -> forEach (seenSet st) $ \eq ->
                        case eq of
                            Equation subst' (TVar x') y | x' == b'
                                -> addEquation (Equation (substCombine subst subst') sub y)
                            _   -> return ()
        _ -> return ()


reduce :: Integer -> [Equation] -> IO [Equation]
reduce start eqs = fmap (Set.toList . seenSet) 
                 $ execStateT (mapM_ addEquation eqs)
                 $ ComputeState { varCounter    = start
                                , seenSet       = Set.empty
                                , substitutions = Map.empty
                                }
