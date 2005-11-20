{-# OPTIONS_GHC -fglasgow-exts #-}

module Funlog.Solve (
    Solution(..),
    solve,
) where

import Funlog.AST

data Rule = Rule {
                ruleSubs :: [Class],
                ruleFun  :: [Item -> Item] -> Item -> Item,
                ruleSol  :: [Solution] -> Solution
            }

data Solution = Solution {
                    solName :: String,
                    solParams :: [Solution]
                }

instance Show Solution where
    show s = solName s ++ if not (null $ solParams s) then " " ++ show (solParams s) else ""

insert :: Int -> a -> [a] -> [a]
insert 0 a xs     = a:xs
insert n a []     = error "insert: list too short"
insert n a (x:xs) = x : insert (n-1) a xs

delete :: Int -> [a] -> [a]
delete 0 (x:xs)   = xs
delete n []       = error "delete: list too short"
delete n (x:xs)   = x : delete (n-1) xs

expand :: Rule -> [Rule]
expand r = concat [expandClass sub idx | sub <- ruleSubs r | idx <- [0..]]
    where
    expandClass :: Class -> Int -> [Rule]
    expandClass sub idx = do
        rcase <- classCases sub
        let nsubs = length $ caseSubs rcase
        return $ Rule {
            ruleSubs = caseSubs rcase ++ delete idx (ruleSubs r),
            ruleFun  = (\fs -> let (these,those) = splitAt nsubs fs
                                   subfun = caseFun rcase these in
                               ruleFun r (insert idx subfun those)),
            ruleSol = (\ss -> let (these,those) = splitAt nsubs ss
                                  subsol = Solution { 
                                             solName = caseName rcase, 
                                             solParams = these
                                           } in
                              ruleSol r (insert idx subsol those))             
        }

closure :: (a -> [a]) -> [a] -> [a]
closure f init = let closed = init ++ concatMap f closed in closed

findFuncs :: Item -> Item -> [Rule] -> [Rule]
findFuncs x y rs = filter (\r -> null (ruleSubs r) && ruleFun r [] x == y) rs

solve :: Item -> Item -> Class -> [Solution]
solve x y cl = map (flip ruleSol []) $ findFuncs x y $ closure expand [initRule]
    where
    initRule = Rule {
                ruleSubs = [cl],
                ruleFun  = head,
                ruleSol  = head
               }
