{-# OPTIONS_GHC -fglasgow-exts #-}

module AGM.ASMCore
    ( Condition
    , Action
    , MonadASM, naughtyLiftIO
    , SVR, SVW, SV
    , newSV, temporalFold
    , ReadVar, WriteVar
    , getVar, writeVar
    , Rule
    , (==>), tag
    , ASMContext
    , newASMContext
    , stepASM
    , initAction
    )
where

import AGM.WFQueue
import Control.Concurrent.STM
import Data.Unique
import Data.Monoid
import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Control.Applicative
import qualified Control.Monad.RWS as RWS
import qualified Control.Monad.Error as Error
import qualified Data.Map as Map
import qualified Data.Set as Set

type Gen = Int
type VarID = Unique

-- Read/Write logs for conditions and actions --

newtype ReadLog 
    = ReadLog [VarID]
    deriving (Monoid)

data WriteLogEntry where
    WriteLogEntry :: VarID -> TWriter (Gen,a) -> a -> WriteLogEntry

newtype WriteLog 
    = WriteLog [WriteLogEntry]
    deriving (Monoid)

data RWLog = RWLog ReadLog WriteLog

instance Monoid RWLog where
    mempty = RWLog mempty mempty
    mappend (RWLog a b) (RWLog a' b') = 
        RWLog (mappend a a') (mappend b b')

class LogRead r where
    logRead :: VarID -> r

class LogWrite w where
    logWrite :: VarID -> TWriter (Gen,a) -> a -> w

instance LogRead ReadLog where
    logRead v = ReadLog [v]

instance LogWrite WriteLog where
    logWrite v writer x = WriteLog [WriteLogEntry v writer x]

instance LogRead RWLog where
    logRead v = RWLog (logRead v) mempty

instance LogWrite RWLog where
    logWrite v writer x = RWLog mempty (logWrite v writer x)


-- Condition and Action monads --

instance Error.Error () where
    noMsg = ()
    strMsg _ = ()

newtype Condition a 
    = Condition (RWS.RWST Gen ReadLog () (Error.ErrorT () IO) a)
    deriving (Functor, Monad)

newtype Action a
    = Action (RWS.RWST Gen RWLog () IO a)
    deriving (Functor, Monad)

-- MonadASM: functionality available in both the Condition and
-- Action monads

class (Functor m, Monad m) => MonadASM m where
    naughtyLiftIO :: IO a -> m a  -- like liftIO, but not exported
    getGeneration :: m Gen
    logReadM :: VarID -> m ()

instance MonadASM Condition where
    naughtyLiftIO = Condition . liftIO
    getGeneration = Condition RWS.ask
    logReadM = Condition . RWS.tell . logRead

instance MonadASM Action where
    naughtyLiftIO = Action . liftIO
    getGeneration = Action RWS.ask
    logReadM = Action . RWS.tell . logRead

logWriteM :: VarID -> TWriter (Gen,a) -> a -> Action ()
logWriteM varid writer v = Action $
    RWS.tell (logWrite varid writer v)

-- Variables


data Version a
    = Version { verRead    :: a
              , verAdvance :: (MonadASM m) => Gen -> m (Version a)
              } 

newtype SVR a 
    = SVR { svrRead :: (MonadASM m) => m (Version a) }

newtype SVW a
    = SVW { svwWrite :: a -> Action () }

data SV a 
    = SV { svR :: SVR a
         , svW :: SVW a
         }

newSV :: forall a. a -> Action (SV a)
newSV init = do
    gen <- getGeneration
    (writer, follower) <- stm $ do
        (writer, follow) <- newWFQueue (gen,init)
        v <- newTVar follow
        return (writer, v)

    varid <- naughtyLiftIO $ newUnique

    let svw = logWriteM varid writer
    let svr :: MonadASM m => m (Version a) 
        svr = do
            gen <- getGeneration
            logReadM varid
            f <- stm $ do
                f' <- advanceFollower =<< readTVar follower
                writeTVar follower f'
                return f'
            return $ version gen f
    return $ SV { svR = SVR svr, svW = SVW svw }
    
    where

    -- advance follower to latest generation
    advanceFollower f = do
        next <- nextFollower f
        case next of
             Nothing -> return f
             Just f' -> advanceFollower f'

    version :: Gen -> TFollower (Gen,a) -> Version a
    version gen follower = Version
        { verRead    = snd $ readFollower follower
        , verAdvance = advance follower
        }

    advance :: (MonadASM m) => TFollower (Gen,a) -> Gen -> m (Version a)
    advance follower gen = do
        next <- stm $ nextFollower follower
        case next of
             Nothing -> return $ version gen follower
             Just f'
                | fst (readFollower f') > gen 
                     -> return $ version gen follower
                | otherwise
                     -> advance f' gen

instance Functor Version where
    fmap f v = Version { verRead = f (verRead v)
                       , verAdvance = fmap (fmap f) . verAdvance v
                       }

instance Applicative Version where
    pure x  = Version { verRead = x
                      , verAdvance = const (return $ pure x)
                      }
    -- this method is dubious, it really only makes
    -- sense if the two objects represent the same
    -- version.  As an intermediate to SVR it may
    -- work though.
    f <*> v = Version { verRead = verRead f (verRead v)
                      , verAdvance = \g -> do
                          f' <- verAdvance f g
                          v' <- verAdvance v g
                          return (f' <*> v')
                      }

instance Functor SVR where
    fmap f v = SVR { svrRead = fmap (fmap f) $ svrRead v }

instance Applicative SVR where
    pure x = SVR { svrRead = return (pure x) }
    f <*> v = SVR { svrRead = do
                        f' <- svrRead f
                        v' <- svrRead v
                        return (f' <*> v')
                  }

stm :: (MonadASM m) => STM a -> m a
stm = naughtyLiftIO . atomically

temporalFold :: forall v a b. (ReadVar v) 
             => (a -> b -> b) -> b -> v a -> Action (SVR b)
temporalFold f init v = do
    gen <- getGeneration
    (writer,follower) <- stm $ do
        (writer,follow) <- newWFQueue (gen,init)
        f <- newTVar follow
        return (writer,f)
    buddy <- readVar v
    let svr :: (MonadASM m) => m (Version b)
        svr = do
            gen <- getGeneration
            f <- stm $ readTVar follower
            advance gen writer buddy f
    return $ SVR svr
    where
    advance :: (MonadASM m) => Gen -> TWriter (Gen,b) -> Version a -> TFollower (Gen,b) -> m (Version b)
    advance gen writer buddy follower = do
        let (gen', v) = readFollower follower
        if gen' == gen
           then return $ Version { verRead = v
                                 , verAdvance = \g -> advance g writer buddy follower
                                 }
           else do
               next <- stm $ nextFollower follower
               case next of
                    Just f' -> advance gen writer buddy f'
                    Nothing -> do
                        buddy' <- verAdvance buddy (gen'+1)
                        let newval = f (verRead buddy') v
                        f' <- stm $ do
                            -- this bullshit is to ensure proper behavior
                            -- in the face of concurrency
                            next' <- nextFollower follower
                            case next' of
                                 Nothing -> appendWriter writer (gen'+1, newval)
                                 Just f' -> return ()
                            Just f' <- nextFollower follower
                            return f'
                        advance gen writer buddy' f'

-- ReadVar: allow using readVar on both SVRs and SVs

class ReadVar v where
    readVar :: (MonadASM m) => v a -> m (Version a)

instance ReadVar SVR where
    readVar = svrRead

instance ReadVar SV where
    readVar = svrRead . svR

getVar :: (ReadVar v, MonadASM m) => v a -> m a
getVar v = do
    gen <- getGeneration
    ver <- readVar v
    ver' <- verAdvance ver gen
    return (verRead ver')

-- WriteVar: allow using writeVar on both SVWs and SVs

class WriteVar v where
    writeVar :: v a -> a -> Action ()

instance WriteVar SVW where
    writeVar = svwWrite

instance WriteVar SV where
    writeVar = svwWrite . svW


-- Rules

data Rule
    = Rule { ruleTag       :: String 
           , ruleCondition :: Condition Bool
           , ruleAction    :: Action ()
           }

(==>) :: Condition Bool -> Action () -> Rule
(==>) = Rule ""

tag :: String -> Rule -> Rule
tag t r = r { ruleTag = t }

-- Execution Context

type RuleID = Unique

data ASMContext
    = ASMContext { 
        -- associate a unique identifier to each rule
        cxtRules    :: Map.Map RuleID Rule,
        -- the generation of the last iteration
        cxtGen      :: Gen,
        -- these rules fired last iteration
        cxtFired    :: Set.Set RuleID,
        -- these variables were modified by actions last iteration
        cxtModified :: Set.Set VarID,
        -- associate to each variable a set of rules whose conditions
        -- depended on it last iteration
        cxtCondDep  :: Map.Map VarID (Set.Set RuleID)
     }

newASMContext :: [Rule] -> IO ASMContext
newASMContext rules = do
    idrules <- forM rules $ \rule -> do
                   id <- newUnique
                   return (id, rule)
    
    let rulesmap = Map.fromList idrules

    -- look out, cxtGen is preventing multiple ASMs working on the same
    -- set of variables.  Maybe it should be global?
    return $ ASMContext 
        { cxtGen      = 1
        , cxtRules    = rulesmap
        -- we say all rules fired so that all rules are checked
        -- upon the first iteration
        , cxtFired    = Map.keysSet rulesmap
        , cxtModified = Set.empty
        , cxtCondDep  = Map.empty
        }

stepASM :: ASMContext -> IO ASMContext
stepASM cxt = do
    -- first find the set of rules we wish to execute
    let to_execute = image (cxtCondDep cxt) (cxtFired cxt)
                   `Set.union` cxtFired cxt
    let rules = concatMap (\x -> 
                    fmap ((,) x) $ Map.lookup x $ cxtRules cxt)
              $ Set.elems to_execute
    let gen = cxtGen cxt

    -- check and execute each rule, for each one recording
    -- ( the rule id
    -- , whether it fired
    -- , the set of variables its condition depended on
    -- , its write log
    -- )
    results <- forM rules $ \(ruleid, Rule _ condition action) -> do
        (cond, deps) <- checkCondition gen condition
        if cond
           then do
               ((), writelog) <- runAction gen action
               return (ruleid, True, deps, writelog)
           else do
               return (ruleid, False, deps, mempty)

    -- check for update contention
    let updates = map (\(ruleid,_,_,log) -> (ruleid,log)) results
    

    let violators = [ (getTag xid, getTag yid) 
                    | (xid,xlog) <- updates
                    , (yid,ylog) <- updates
                    , xid /= yid
                    , let xvars = varsInLog xlog
                    , let yvars = varsInLog ylog
                    , not (Set.null (xvars `Set.intersection` yvars))
                    ]
    when (not $ null violators) $ do
        fail $ "Update contention in rules: " ++ show violators

    -- perform updates
    atomically $ commitLog (gen+1) $ mconcat $ map snd updates

    -- calculate next context
    return $ ASMContext
        { cxtGen = gen+1
        , cxtRules = cxtRules cxt
        , cxtFired = 
            Set.fromList [ ruleid | (ruleid, True, _, _) <- results ]
        , cxtModified = 
            Set.unions $ map varsInLog $ map snd $ updates
        , cxtCondDep =
            Map.unionsWith Set.union
                [ Map.unionsWith Set.union maps
                | (ruleid, _, deps, _) <- results
                , let maps = map (\dep -> Map.singleton dep (Set.singleton ruleid)) 
                           $ Set.elems deps
                ]
        }

    where
    image :: (Ord k, Ord v) => Map.Map k (Set.Set v) -> Set.Set k -> Set.Set v
    image f xs 
        = Set.unions . Set.elems
        $ Set.map fromJust 
        $ Set.map (\x -> Map.lookup x f) xs 
            Set.\\ Set.singleton Nothing
    
    getTag :: RuleID -> String
    getTag id = 
        case Map.lookup id (cxtRules cxt) of
             Nothing -> "(unknown)"
             Just (Rule { ruleTag = tag }) -> tag

    varsInLog :: WriteLog -> Set.Set VarID
    varsInLog (WriteLog log) =
        Set.fromList $ map (\(WriteLogEntry varid _ _) -> varid) log

checkCondition :: Gen -> Condition Bool -> IO (Bool, Set.Set VarID)
checkCondition gen (Condition cond) = do
    let cond' = Error.catchError cond (const $ return False)
    Right (v, (), ReadLog log) <- Error.runErrorT $ RWS.runRWST cond' gen ()
    return (v, Set.fromList log)

runAction :: Gen -> Action a -> IO (a, WriteLog)
runAction gen (Action act) = do
    (v, (), RWLog _ log) <- RWS.runRWST act gen ()
    return (v, log)

initAction :: Action a -> IO a
initAction action = do
    (v, log) <- runAction 0 action
    atomically $ commitLog 1 log
    return v

commitLogEntry :: Gen -> WriteLogEntry -> STM ()
commitLogEntry gen (WriteLogEntry _ writer x) = do
    appendWriter writer (gen, x)

commitLog :: Gen -> WriteLog -> STM ()
commitLog gen (WriteLog l) = do
    sequence_ $ map (commitLogEntry gen) l
