{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader

data Type where
    TAtom  :: String          -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type    -> Type  -- functions
    TTuple :: Type -> Type    -> Type  -- tuples
    TVar   :: Integer         -> Type  -- existential variables
    TGen   :: Integer         -> Type  -- generalized variables
    TLam   :: Integer -> Type -> Type  -- universal types
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
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
substituteType sub (TTuple a b) 
    = TTuple (substituteType sub a) (substituteType sub b)
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

type Compute a = StateT ComputeState (ReaderT Int IO) a

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
            liftIO $ putStrLn $ " *** (" ++ show substid ++ ") Instantiate " ++ show (TGen g) ++ " ==> " ++ show (TVar newvar)
            insertSubst substid (TGen g) (TVar newvar)
            return $ TVar newvar
instantiateGen substid (TArrow a b) = do
    a' <- instantiateGen substid a
    b' <- instantiateGen substid b
    return $ TArrow a b
instantiateGen substid (TTuple a b) = do
    a' <- instantiateGen substid a
    b' <- instantiateGen substid b
    return $ TTuple a b
instantiateGen substid (TLam v t) = do
    -- this is safe because you can't lambda over a Gen
    t' <- instantiateGen substid t
    return $ TLam v t' 
instantiateGen _ x = return x

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

twoColumn :: Int -> String -> String -> String
twoColumn width cola colb 
    = cola ++ replicate spaces ' ' ++ colb
    where
    spaces = if length cola + 4 < width
                 then width - length cola
                 else 4

addEquation :: String -> Equation -> Compute ()
addEquation reason eq@(Equation substid a b) = do
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
            depth <- ask
            liftIO $ putStrLn (maybe " " show substid ++ ")  " ++ twoColumn 50 (concat (replicate depth "  ") ++ show toAdd) ("(" ++ reason ++ ")"))
            local (+1) $ transformEquation toAdd
            st <- get
            put (st { seenSet = Set.insert toAdd (seenSet st) })
    

substCombine :: Maybe SubstID -> Maybe SubstID -> Maybe SubstID
substCombine Nothing Nothing = Nothing
substCombine Nothing (Just a) = Just a
substCombine (Just a) Nothing = Just a
substCombine (Just a) (Just b) 
    | a == b    = Just a
    | otherwise = error "Attempt to combine two substitution ids (I don't know what to do yet)"

transformEquation :: Equation -> Compute ()
transformEquation (Equation subst (TArrow a b) (TArrow a' b')) = do
    addEquation "arrow" (Equation subst a' a)
    addEquation "arrow" (Equation subst b b')
transformEquation (Equation subst (TTuple a b) (TTuple a' b')) = do
    addEquation "tuple" (Equation subst a a')
    addEquation "tuple" (Equation subst b b')
transformEquation (Equation subst sub@(TLam v t) sup) = do
    sub' <- instantiateLam sub
    addEquation "instantiate" (Equation subst sub' sup)
transformEquation (Equation subst sub sup@(TLam v t)) = do
    sup' <- generalizeLam sup
    addEquation "generalize" (Equation subst sub sup')
transformEquation (Equation subst sub sup) = do
    st <- get
    
    case sub of
        TVar a' -> forEach (seenSet st) $ \eq -> 
                        case eq of
                            Equation subst' x (TVar y') | y' == a'
                                -> addEquation "left-elim" (Equation (substCombine subst subst') x sup)
                            _   -> return ()
        _ -> return ()
    
    case sup of
        TVar b' -> forEach (seenSet st) $ \eq ->
                        case eq of
                            Equation subst' (TVar x') y | x' == b'
                                -> addEquation "right-elim" (Equation (substCombine subst subst') sub y)
                            _   -> return ()
        _ -> return ()


reduce :: Integer -> [Equation] -> IO [Equation]
reduce start eqs = fmap (Set.toList . seenSet) 
                 $ flip runReaderT 0
                 $ execStateT (mapM_ (addEquation "init") eqs)
                 $ ComputeState { varCounter    = start
                                , seenSet       = Set.empty
                                , substitutions = Map.empty
                                }

main :: IO ()
main = do
    reduced <- reduce 100 eqs
    putStrLn ""
    mapM_ print reduced
    where
          --    a -> b        <:  \a (a -> a)
    eqs = [ Equation Nothing (TArrow (TVar 0) (TVar 1)) (TLam 0 (TArrow (TVar 0) (TVar 0)))
          --    \a (a -> a)   <:  a -> b
          , Equation Nothing (TLam 0 (TArrow (TVar 0) (TVar 0))) (TArrow (TVar 0) (TVar 1))
          -- .1 c             <:  d -> e
          , Equation (Just 0) (TVar 2) (TArrow (TVar 3) (TVar 4))
          --    Int           <:  d
          , Equation Nothing (TAtom "Int") (TVar 3)
          -- .2 c             <:  f -> g
          , Equation (Just 1) (TVar 2) (TArrow (TVar 5) (TVar 6))
          --    Str           <:  f
          , Equation Nothing (TAtom "Str") (TVar 5)
          -- *? c -> (e,g)    <:  h -> i
          , Equation Nothing (TArrow (TVar 2) (TTuple (TVar 4) (TVar 6))) (TArrow (TVar 7) (TVar 8))
          --    a -> b        <:  h
          , Equation Nothing (TArrow (TVar 0) (TVar 1)) (TVar 7)
          ]
