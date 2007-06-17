{-# OPTIONS_GHC -fglasgow-exts #-}

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified Control.Monad as Monad
import qualified System.Random as Random

data Term
    = TVar String
    | TFunc String [Term]

data Formula
    = FRelation String [Term]
    | FEquals Term Term
    | FAnd Formula Formula
    | FNot Formula
    | FForAll String Formula

data Function a
    = Function { fArity  :: Int
               , fValues :: Map.Map [a] a 
               }

data Relation a
     = Relation { rArity  :: Int
                , rValues :: Set.Set [a] 
                }

data Model a
    = Model { mUniverse  :: Set.Set a
            , mFunctions :: Map.Map String (Function a)
            , mRelations :: Map.Map String (Relation a) 
            }

type Pad a = Map.Map String a
type Interpret v a = Reader.Reader (Pad v) a

resolve :: (Ord v, ?m :: Model v) => Term -> Interpret v v
resolve (TVar x) = Map.lookup x =<< Reader.ask
resolve (TFunc fname xs) = do
    let f = mFunctions ?m Map.! fname
    Monad.when (length xs /= fArity f) $ fail $ "Wrong arity for function " ++ fname
    xs' <- mapM resolve xs
    Map.lookup xs' (fValues f)

interpret :: (Ord v, ?m :: Model v) => Formula -> Interpret v Bool
interpret (FRelation rname xs) = do
    let r = mRelations ?m Map.! rname
    Monad.when (length xs /= rArity r) $ fail $ "Wrong arity for relation " ++ rname
    xs' <- mapM resolve xs
    return (xs' `Set.member` rValues r)
interpret (FEquals s t) = do
    s' <- resolve s
    t' <- resolve t
    return (s' == t')
interpret (FAnd p q) = do
    p' <- interpret p
    q' <- interpret q
    return (p' && q')
interpret (FNot p) = do
    p' <- interpret p
    return (not p')
interpret (FForAll v p) = do
    let elems = Set.elems (mUniverse ?m)
    truths <- mapM (\e -> Reader.local (Map.insert v e) (interpret p)) elems
    return (and truths)

interpretFormula :: (Ord v) => Model v -> Formula -> Bool
interpretFormula m f = let ?m = m in Reader.runReader (interpret f) Map.empty
