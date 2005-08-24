-- from code/perl/type_inference/closure.pl

import Control.Monad.State
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Queue


data Type = Type String
          | List Type
    deriving (Show, Eq, Ord)

data Rule = Does Type Type
    deriving (Show, Eq, Ord)

-- Fall back on procedural methods, because I don't know how to think
-- this functionally :-(

data CS = CS (Queue Rule) (Set Rule)

insert_rule :: Rule -> State CS ()
insert_rule rule = do
    CS queue closure <- get
    unless (rule `Set.member` closure) $ do
        put (CS (addToQueue queue rule) (Set.insert rule closure))

replace :: Type -> Type -> Type -> Maybe Type
replace typ pat repl 
    | pat == typ        = Just repl
    | List inner <- typ = replace inner pat repl >>= Just . List
    | otherwise         = Nothing

process :: Rule -> State CS ()
process rule = do
    CS _ closure <- get
    sequence_ $ map (\subrule -> do
                        luni subrule rule
                        runi subrule rule) 
                    (Set.elems closure)
    where
    luni :: Rule -> Rule -> State CS ()
    luni (Does subrulel subruler) (Does t@(Type _) ruler) = 
        maybe (return ())
              (\repl -> insert_rule (Does repl subruler))
              (replace subrulel ruler t)
    luni _ _ = return ()
    
    runi :: Rule -> Rule -> State CS ()
    runi (Does subrulel subruler) (Does rulel t@(Type _)) = 
        maybe (return ())
              (\repl -> insert_rule (Does subrulel repl))
              (replace subruler rulel t)
    runi _ _ = return ()

close_ :: State CS (Set Rule)
close_ = do
    CS queue closure <- get
    maybe (return closure)
          (\(e, newq) -> do
              put (CS newq closure)
              process e
              close_)
          (deQueue queue)

close :: [Rule] -> [Rule]
close rules = Set.toList $ fst $ runState close_ $ 
                CS (listToQueue rules) (Set.fromList rules)

main :: IO ()
main = sequence_ $ map print $ close rules
    where
    rules :: [Rule]
    rules = [
        Does (Type "a") (List $ Type "a"),
        Does (List $ List $ Type "a") (Type "Num"),
        Does (Type "c") (Type "a") ]
