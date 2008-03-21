import Control.Monad.State
import qualified Data.Sequence as Seq
import qualified Data.Map as Map

-- lambda calculus with conjunctive types

data PrimType
    = PrimInt
    | PrimBool
    deriving (Eq,Show)

data Type
    = TPrim PrimType
    | TFunc Type Type
    | TConj [Type]
    | TVar  Int
    deriving (Eq,Show)

data Constraint = Type :< Type

solveConstraints :: Seq.Seq Constraint -> Map.Map Int Type
solveConstraints = undefined
    where
    newVar = do
        (m,v) <- get
        v `seq` put (m, v+1)
        return $ TVar v
    writeSubst v t = do
        (m,c) <- get
        m `seq` put (Map.insert v t m, c)
    solve s = do
        case Seq.viewl s of
            Seq.EmptyL -> return ()
            x Seq.:< xs -> do
                (m,_) <- get
                rest <- solve1 (subst m x)
                solve $ xs `mappend` rest

    solve1 (TPrim p :< TPrim p') = do
        when (p /= p') $ fail $ "Cannot unify " ++ show p ++ " with " ++ show p'

    solve1 (TFunc a b :< TFunc a' b') = do
        return $ Seq.fromList [ b :< b', a' :< a ]
    solve1 (TFunc a b :< TVar v) = do
        va <- newVar
        vb <- newVar
        writeSubst v (TFunc va vb)
        return $ Seq.fromList [ b :< vb, va :< a ]

    solve1 (TVar v :< TPrim p) = writeSubst v (TPrim p) >> return mempty
    solve1 (TVar v :< TFunc a b) = do
        va <- newVar
        vb <- newVar
        writeSubst v (TFunc va vb)
        return $ Seq.fromList [ vb :< b, a :< va ]
    solve1 (TVar v :< TVar v') = return $ Seq.singleton (TVar v :< TVar v')

    solve1 (t :< TConj ts) = do
        return $ Seq.fromList $ map (t :<) ts
