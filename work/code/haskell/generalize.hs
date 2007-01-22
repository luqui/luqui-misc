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
    TVar   :: Integer -> Bool    -> Type  -- singular types
    TSup   :: Integer            -> Type  -- supremum type (base, inst)
    TInf   :: Integer            -> Type  -- infimum type  (base, inst)
    TLam   :: Integer -> Type    -> Type  -- universal types
    deriving (Eq,Ord)

instance Show Type where
    show (TAtom  a)   = a
    show (TArrow a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
    show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TVar v _)   = show v
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
    = TLam v (substituteType (Map.delete (TVar v False) sub) t)
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
    return $ substituteType (Map.singleton (TVar v False) (TVar newvar False)) t
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
            st <- get
            put (st { seenSet = Set.insert eq (seenSet st) })
            local (+1) $ transformEquation eq
    

-- x <: inf a  ok
-- inf a <: x  inst
-- sup a <: x  ok
-- x <: sup a  inst

generatedVar :: Type -> Bool
generatedVar (TVar _ True) = True
generatedVar _ = False
    
isLim :: Type -> Bool
isLim (TInf _) = True
isLim (TSup _) = True
isLim (TLam _ _) = True
isLim _ = False

transformEquation :: Equation -> Compute ()
transformEquation (Equation (TArrow a b) (TArrow a' b')) = do
    addEquation "arrow" (Equation a' a)
    addEquation "arrow" (Equation b b')
    
transformEquation (Equation (TTuple a b) (TTuple a' b')) = do
    addEquation "tuple" (Equation a a')
    addEquation "tuple" (Equation b b')

transformEquation (Equation sub@(TLam v t) sup) | not (isLim sup) = do
    sub' <- instantiateLam sub
    addEquation "instantiate" (Equation sub' sup)

transformEquation (Equation (TInf a) b) | not (generatedVar b) && not (isLim b) = do
    newvar <- allocateVar
    addEquation "infiumum" (Equation (TInf a) (TVar newvar True))
    addEquation "infiumum" (Equation (TVar newvar True) b)
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation x (TInf y') | y' == a
                        -> addEquation ("infiumum carry") (Equation x (TVar newvar True))
                    _   -> return ()

transformEquation (Equation a (TInf b)) = do
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation (TInf x') y | x' == b
                        -> addEquation ("infimum carry") (Equation a y)
                    _   -> return ()

transformEquation (Equation a (TSup b)) | not (generatedVar a) && not (isLim a) = do
    newvar <- allocateVar
    addEquation "supremum" (Equation (TVar newvar True) (TSup b))
    addEquation "supremum" (Equation a (TVar newvar True))
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation (TSup x') y | x' == b
                        -> addEquation ("supremum carry") (Equation (TVar newvar True) y)
                    _   -> return ()

transformEquation (Equation (TSup a) b) = do
    st <- get
    forEach (seenSet st) $ \eq ->
                case eq of
                    Equation x (TSup y') | y' == a
                        -> addEquation ("supremum carry") (Equation x b)
                    _   -> return ()

transformEquation (Equation sub sup) = do
    st <- get
    
    case sub of
        TVar a' _ -> forEach (seenSet st) $ \eq -> 
                        case eq of
                            Equation x (TVar y' _) | y' == a'
                                -> addEquation ("left-elim  " ++ show sub) (Equation x sup)
                            _   -> return ()
        _ -> return ()
    
    case sup of
        TVar b' _ -> forEach (seenSet st) $ \eq ->
                        case eq of
                            Equation (TVar x' _) y | x' == b'
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

-- Okay, in order for this algorithm to work (empirically -- the code
-- is hacked up in order to ensure termination of *this* example, and
-- is certainly far from proof of decidability), you need to mark 
-- your types as singular, infimum, or supremum.  Mark too few,
-- the algorithm will happily generalize too much; mark too many,
-- the algorithm will not be able to discover anything.

-- When creating functions \x { ... } :: a -> b, a may be marked
-- an infimum type and b a supremum type without loss of expression.
-- That is because an argument to the function of type c will come
-- in via the equation c <: a, which is universal for any infimum
-- type a (c <: every member of a's defining set).  Similar reasoning
-- works for the return type.

-- Is it possible to mark every type variable in your program as either 
-- inf or sup, but not both?  The one I'm worried about is 
-- a <: \a (a -> a) (equation 1) below.  This was generated by the
-- expression (\x { x } :: forall a. a -> a).  But \x { x } is a lambda,
-- so it comes out saying its type is x -> y for some x and y.  I 
-- manually changed that to an inf type, knowing that it was (note to
-- self, it works as a sup type, too).  What can the compiler do to 
-- determine this?

main :: IO ()
main = do
    reduced <- reduce 100 eqs
    putStrLn ""
    mapM_ print reduced
    where
    tVar :: Integer -> Type
    tVar i = TVar i False

          --    a             <:  \a (a -> a)
    eqs = [ Equation (TSup 0) (TLam 0 (TArrow (tVar 0) (tVar 0)))
          --    \a (a -> a)   <:  a
          , Equation (TLam 0 (TArrow (tVar 0) (tVar 0))) (TSup 0)
          -- .1 c             <:  d -> e
          , Equation (TInf 2) (TArrow (TInf 3) (TSup 4))
          --    Int           <:  d
          , Equation (TAtom "Int") (TInf 3)
          -- .2 c             <:  f -> g
          , Equation (TInf 2) (TArrow (TInf 5) (TSup 6))
          --    Str           <:  f
          , Equation (TAtom "Str") (TInf 5)
          -- *? c -> (e,g)    <:  h -> i
          , Equation (TArrow (TInf 2) (TTuple (TSup 4) (TSup 6))) (TArrow (TInf 7) (TSup 8))
          --    a             <:  h
          , Equation (TSup 0) (TInf 7)
          ]
