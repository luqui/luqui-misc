module Closure (
    close,
) where

import Control.Monad.State
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Queue

import Type

data CS = CS (Queue Rule) (Set Rule)

insert_rule :: Rule -> State CS ()
insert_rule rule = do
    CS queue closure <- get
    unless (rule `Set.member` closure) $ do
        put (CS (addToQueue queue rule) (Set.insert rule closure))

replace :: Type -> Type -> Type -> Maybe Type
replace pat with target 
    | target == pat  = Just with
    | otherwise      = gut (replace pat with) target

process :: Rule -> State CS ()
process rule = do
    CS _ closure <- get
    sequence_ $ map (\subrule -> do
                        luni subrule rule
                        runi subrule rule) 
                    (Set.elems closure)
    where
    luni :: Rule -> Rule -> State CS ()
    luni (Does subrulel subruler) (Does t@(Type _ _) ruler) = 
        maybe (return ())
              (\repl -> insert_rule (Does repl subruler))
              (replace ruler t subrulel)
    luni _ _ = return ()
    
    runi :: Rule -> Rule -> State CS ()
    runi (Does subrulel subruler) (Does rulel t@(Type _ _)) = 
        maybe (return ())
              (\repl -> insert_rule (Does subrulel repl))
              (replace rulel t subruler)
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
