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
    TVar   :: Integer            -> Type  -- singular type
    TLim   :: Integer            -> Type  -- limit type
    TLam   :: Integer -> Type    -> Type  -- universal type
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
    show (TLam i t)   = "\\" ++ show i ++ " " ++ show t

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
isLim (TLim _) = True
isLim (TLam _ _) = True
isLim _ = False

transformEquation :: Equation -> Compute ()
transformEquation (TArrow a b :< TArrow a' b') = do
    addEquation "arrow" (a' :< a)
    addEquation "arrow" (b :< b')
    
transformEquation (TTuple a b :< TTuple a' b') = do
    addEquation "tuple" (a :< a')
    addEquation "tuple" (b :< b')

transformEquation (sub@(TLam v t) :< sup) | not (isLim sup) = do
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
    eqs = [ TLim 4                            :< TArrow (TLim 0) (TLim 3)
          , TLam 0 (TArrow (TVar 0) (TVar 0)) :< TLim 0
          , TTuple (TLim 1) (TLim 2)          :< TLim 3
          , TLim 0                            :< TArrow (TLim 5) (TLim 1)
          , TAtom "Int"                       :< TLim 5
          , TLim 0                            :< TArrow (TLim 6) (TLim 2)
          , TAtom "Str"                       :< TLim 6
          ]
