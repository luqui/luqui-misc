-- from code/perl/type_inference/closure.pl

import Control.Monad.State

data Type = Type String
          | List Type
    deriving (Show, Eq)

data Rule = Does Type Type
    deriving (Show, Eq)

rules :: [Rule]
rules = [
    Does (Type "a") ((List . Type) "a"),
    Does ((List . List . Type) "a") (Type "Num"),
    Does (Type "c") (Type "a") ]

-- Fall back on procedural methods, because I don't know how to think
-- this functionally :-(

data CS = CS [Rule] [Rule]

insert_rule :: Rule -> State CS ()
insert_rule rule = do
    CS queue closure <- get
    unless (rule `elem` closure) $ do
        put (CS (queue ++ [rule]) (rule:closure))

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
                    closure
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

close :: State CS [Rule]
close = do
    CS queue closure <- get
    if length queue > 0
        then let (q:qs) = queue in do
            put (CS qs closure)
            process q
            close
        else return closure

main :: IO ()
main = let closure = fst $ runState close $ CS rules rules in
           sequence_ (map print closure)
