{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader

data Type where
    TAtom  :: String             -> Type  -- Int, Top, etc.
    TArrow :: Type -> Type       -> Type  -- functions
    TTuple :: Type -> Type       -> Type  -- tuples
    TVar   :: Integer            -> Type  -- singular types
    TSup   :: Integer            -> Type  -- supremum type (base, inst)
    TInf   :: Integer            -> Type  -- infimum type  (base, inst)
    TLam   :: Integer -> Type    -> Type  -- universal types
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar   v)   = show v
    show (TSup   v)   = "v" ++ show v
    show (TInf   v)   = "^" ++ show v
    show (TLam i t)   = "\\" ++ show i ++ " " ++ show t

type Subst = Map.Map Type Type
type SubstID = Integer

data Equation where
    Equation :: Type -> Type -> Equation
    deriving (Eq,Ord)

instance Show Equation where
    show (Equation a b) = show a ++ " <: " ++ show b


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
        } :: ComputeState

type Compute a = StateT ComputeState (ReaderT Int IO) a

allocateVar :: Compute Integer
allocateVar = do
    ret <- fmap varCounter get
    modify $ \st -> st { varCounter = ret + 1 }
    return ret


instantiateLam :: Type -> Compute Type
instantiateLam (TLam v t) = do
    newvar <- allocateVar
    return $ substituteType (Map.singleton (TVar v) (TVar newvar)) t
instantiateLam _ = error "Tried to lambda-instantiate a non-lambda"

twoColumn :: Int -> String -> String -> String
twoColumn width cola colb 
    = cola ++ replicate spaces ' ' ++ colb
    where
    spaces = if length cola + 4 < width
                 then width - length cola
                 else 4

addEquation :: String -> Equation -> Compute ()
addEquation reason eq@(Equation a b) = do
    st <- get
    if eq `Set.member` seenSet st
        then return ()
        else do
            depth <- ask
            liftIO $ putStrLn (twoColumn 50 (concat (replicate depth "  ") ++ show eq) ("(" ++ reason ++ ")"))
            local (+1) $ transformEquation eq
            st <- get
            put (st { seenSet = Set.insert eq (seenSet st) })
    

-- x <: inf a  ok
-- inf a <: x  inst
-- sup a <: x  ok
-- x <: sup a  inst

transformEquation :: Equation -> Compute ()
transformEquation (Equation (TArrow a b) (TArrow a' b')) = do
    addEquation "arrow" (Equation a' a)
    addEquation "arrow" (Equation b b')
    
transformEquation (Equation (TTuple a b) (TTuple a' b')) = do
    addEquation "tuple" (Equation a a')
    addEquation "tuple" (Equation b b')

transformEquation (Equation sub@(TLam v t) sup) = do
    sub' <- instantiateLam sub
    addEquation "instantiate" (Equation sub' sup)

transformEquation (Equation (TInf a) b) = do
    newvar <- allocateVar
    addEquation "infiumum" (Equation (TInf a) (TVar newvar))
    addEquation "infiumum" (Equation (TVar newvar) b)
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation x (TInf y') | y' == a
                        -> addEquation ("infiumum carry") (Equation x (TVar newvar))
                    _   -> return ()

transformEquation (Equation a (TSup b)) = do
    newvar <- allocateVar
    addEquation "supremum" (Equation (TVar newvar) (TSup b))
    addEquation "supremum" (Equation a (TVar newvar))
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation (TSup x') y | x' == b
                        -> addEquation ("supremum carry") (Equation (TVar newvar) y)
                    _   -> return ()

transformEquation (Equation sub sup) = do
    st <- get
    
    case sub of
        TVar a' -> forEach (seenSet st) $ \eq -> 
                        case eq of
                            Equation x (TVar y') | y' == a'
                                -> addEquation ("left-elim  " ++ show sub) (Equation x sup)
                            _   -> return ()
        _ -> return ()
    
    case sup of
        TVar b' -> forEach (seenSet st) $ \eq ->
                        case eq of
                            Equation (TVar x') y | x' == b'
                                -> addEquation ("right-elim " ++ show sup) (Equation sub y)
                            _   -> return ()
        _ -> return ()


reduce :: Integer -> [Equation] -> IO [Equation]
reduce start eqs = fmap (Set.toList . seenSet) 
                 $ flip runReaderT 0
                 $ execStateT (mapM_ (addEquation "init") eqs)
                 $ ComputeState { varCounter    = start
                                , seenSet       = Set.empty
                                }

main :: IO ()
main = do
    reduced <- reduce 100 eqs
    putStrLn ""
    mapM_ print reduced
    where
          --    a -> b        <:  \a (a -> a)
    eqs = [ Equation (TArrow (TVar 0) (TVar 1)) (TLam 0 (TArrow (TVar 0) (TVar 0)))
          --    \a (a -> a)   <:  a -> b
          , Equation (TLam 0 (TArrow (TVar 0) (TVar 0))) (TArrow (TVar 0) (TVar 1))
          -- .1 c             <:  d -> e
          , Equation (TInf 2) (TArrow (TVar 3) (TVar 4))
          --    Int           <:  d
          , Equation (TAtom "Int") (TVar 3)
          -- .2 c             <:  f -> g
          , Equation (TInf 2) (TArrow (TVar 5) (TVar 6))
          --    Str           <:  f
          , Equation (TAtom "Str") (TVar 5)
          -- *? c -> (e,g)    <:  h -> i
          , Equation (TArrow (TInf 2) (TTuple (TVar 4) (TVar 6))) (TArrow (TVar 7) (TVar 8))
          --    a -> b        <:  h
          , Equation (TArrow (TVar 0) (TVar 1)) (TVar 7)
          ]
