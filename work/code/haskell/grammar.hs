import Control.Monad.Omega

data Symbol a
    = Terminal a
    | Nonterminal [[Symbol a]]
    deriving Show

testGrammar = s
    where
    s = Nonterminal [[addExpr]]
    addExpr = Nonterminal [[mulExpr], [mulExpr, Terminal '+', addExpr]]
    mulExpr = Nonterminal [[term], [term, Terminal '*', mulExpr]]
    term = Nonterminal [[number], [Terminal '(', s, Terminal ')']]

    digit = Nonterminal $ map (return . Terminal . head . show) [0..9]
    number = Nonterminal [[digit], [digit, number]]


enumerate = runOmega . enumerate'
    where
    enumerate' (Terminal a) = return [a]
    enumerate' (Nonterminal alts) = do
        seq <- each alts
        rep <- mapM enumerate' seq
        return $ concat rep

printy = mapM (\x -> putStrLn x >> getLine)
