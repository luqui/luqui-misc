
data Foo = Foo Foo
         | Nil
    deriving Show

data Root = Root Foo
    deriving Show

data SynFoo = SynFoo { b :: Int, d :: Int }
data InhFoo = InhFoo { a :: Int, c :: Int }

data SynRoot = SynRoot { result :: Int }
data InhRoot = InhRoot

visitFoo :: Foo -> InhFoo -> SynFoo
visitFoo (Foo foo) inh = let vf = visitFoo foo (InhFoo { a = a inh + 1, c = c inh + 1 }) in
                         SynFoo { b = b vf + 1, d = d vf + 1 }
visitFoo Nil inh = SynFoo { b = a inh + 1, d = c inh + 1 }

visitRoot :: Root -> InhRoot -> SynRoot
visitRoot (Root foo) inh = let vf = visitFoo foo (InhFoo { a = d vf + 1, c = b vf + 1 }) in
                           SynRoot { result = d vf }

main :: IO ()
main = do
        putStrLn "Original:"
        print tree
        putStrLn "New:"
        print $ result $ visitRoot tree InhRoot
    where
        tree :: Root
        tree = Root (Foo (Foo (Nil)))
