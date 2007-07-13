{-# OPTIONS_GHC -fglasgow-exts #-}

module AGM
    ( )
where

import qualified Data.Map as Map
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified AGM.Maybe as Maybe
import qualified Data.Maybe as Maybe
import qualified Data.List as List

-- DATA STRUCTURES --

type GameM s a = State.StateT s IO a
type RuleM s a = Maybe.MaybeT (Reader.Reader s) a
type ActionM s a = State.State s a
type InteractiveActionM s a = State.StateT s IO a

type ActionImpl s = Either (ActionM s ()) (InteractiveActionM s ())
data Action s
    = ActionNamed    { actionName :: String
                     , actionImpl :: ActionImpl s
                     }
    | ActionOverride { actionName :: String 
                     , actionImpl :: ActionImpl s
                     }
    | ActionAnon     { actionImpl :: ActionImpl s }

type Rule s = RuleM s [Action s]

-- INTERFACE --

auto :: ActionM s () -> ActionImpl s
auto = Left

manual :: InteractiveActionM s () -> ActionImpl s
manual = Right

action :: String -> ActionImpl s -> Action s
action = ActionNamed 

action_ :: ActionImpl s -> Action s
action_ = ActionAnon

override :: String -> ActionImpl s -> Action s
override = ActionOverride

gameStep :: [Rule s] -> GameM s ()
gameStep rs = do
    actions <- computeActions rs
    let (nonIvs, ivs) = siftActions . filterActions $ actions
    mapM_ runAction $ nonIvs ++ ivs

gameStart :: s -> GameM s a -> IO a
gameStart = flip State.evalStateT

-- IMPLEMENTATION --

runRuleM :: RuleM s a -> s -> Maybe a
runRuleM r s = Reader.runReader (Maybe.runMaybeT r) s

computeActions :: [Rule s] -> GameM s [Action s]
computeActions rs = do
    st <- State.get
    return . concat . Maybe.catMaybes $ map (\r -> runRuleM r st) rs

filterActions :: forall s. [Action s] -> [Action s]
filterActions as = anon ++ Map.elems (foldr overrideInsert Map.empty as)
    where
    overrideInsert :: Action s -> Map.Map String (Action s) -> Map.Map String (Action s)
    overrideInsert a@(ActionNamed {})    = Map.insertWith (flip const) (actionName a) a
    overrideInsert a@(ActionOverride {}) = Map.insert (actionName a) a
    overrideInsert (ActionAnon {})       = id

    (named,anon) = List.partition isNamed as

    isNamed (ActionNamed {})    = True
    isNamed (ActionOverride {}) = True
    isNamed (ActionAnon {})     = False

siftActions :: [Action s] -> ([Action s], [Action s])
siftActions = List.partition (not . isInteractive)
    where
    isInteractive = either (const False) (const True) . actionImpl

runAction :: Action s -> GameM s ()
runAction a = runImpl (actionImpl a)
    where
    runImpl :: ActionImpl s -> GameM s ()
    runImpl (Left m)  = State.modify (State.execState m)
    runImpl (Right m) = m

