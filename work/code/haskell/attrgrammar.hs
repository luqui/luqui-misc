
data Tree = Leaf Int
          | Branch Tree Tree
    deriving Show

data Root = Root Tree
    deriving Show

data SynTree = SynTree { minT :: Int, resultT :: Tree }
data InhTree = InhTree { gminT :: Int }

data SynRoot = SynRoot { resultR :: Tree }
data InhRoot = InhRoot

visitTree :: Tree -> InhTree -> SynTree
visitTree (Leaf x)     inh = SynTree { minT = x, resultT = Leaf (gminT inh) }
visitTree (Branch l r) inh = let lv = visitTree l (InhTree { gminT = gminT inh })
                                 rv = visitTree r (InhTree { gminT = gminT inh }) in
                             SynTree { minT    = min (minT lv) (minT rv),
                                       resultT = Branch (resultT lv) (resultT rv) }

visitRoot :: Root -> InhRoot -> SynRoot
visitRoot (Root tree) inh = let tv = visitTree tree (InhTree { gminT = minT tv }) in
                            SynRoot { resultR = resultT tv }

main :: IO ()
main = do
        putStrLn "Before:"
        print tree
        putStrLn "\nAfter:"
        print $ resultR (visitRoot tree InhRoot)
    where
        tree :: Root
        tree = Root $
                 Branch
                   (Leaf 5)
                   (Branch
                     (Branch
                       (Leaf 2)
                       (Leaf 9))
                     (Leaf 6))
