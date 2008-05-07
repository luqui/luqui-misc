import Control.Monad.Omega

data Symbol a
    = Terminal a
    | Nonterminal [[Symbol a]]
    deriving Show

testGrammar = s
    where
    s = Nonterminal [[addExpr]]
    addExpr = Nonterminal [[mulExpr], [addExpr, Terminal '+', mulExpr]]
    mulExpr = Nonterminal [[term], [mulExpr, Terminal '*', term]]
    term = Nonterminal [[number], [Terminal '(', s, Terminal ')']]

    number = Nonterminal $ map (map Terminal . show) [0..]


enumerate = runOmega . enumerate'
    where
    enumerate' (Terminal a) = return [a]
    enumerate' (Nonterminal alts) = do
        seq <- each alts
        rep <- mapM enumerate' seq
        return $ concat rep

printy = mapM (\x -> putStrLn x >> getLine)
