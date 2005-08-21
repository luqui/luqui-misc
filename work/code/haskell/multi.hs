data Type = Type String
    deriving Show

instance Eq Type where
    (==) a b = a `does` b && b `does` a

data Var  = Var [Type]
    deriving Show

-- XXX this is a PARTIAL order, so it doesn't really
-- satisfy the algebraic constraints of Ord
instance Eq Var where
    (==) a b = a <= b && b <= a

instance Ord Var where
    (<=) (Var va) (Var vb) = 
        and $ map (uncurry does) (va `zip` vb)

does_map :: String -> String -> Bool
-- kernel --
does_map "Str" "Object" = True
does_map "Num" "Object" = True
does_map "Int" "Num" = True
-- closure --
does_map "Int" "Object" = True
-- reflexive --
does_map a b
    | (a == b) = True
does_map _ _ = False

does :: Type -> Type -> Bool
does (Type a) (Type b) = does_map a b

match :: [Var] -> Var -> [Var]
match vs args = [ v | v <- vs, args <= v ]

weed :: [Var] -> [Var]
weed vs = [ v | v <- vs, not $ or [ w < v | w <- vs ] ]

main :: IO ()
main = print $ weed $ match vars args
    where
    vars = [
        Var [ Type "Object", Type "Object" ],
        Var [ Type "Int", Type "Str" ],
        Var [ Type "Num", Type "Int" ],
        Var [ Type "Int", Type "Num" ] ]
    args = Var [ Type "Int", Type "Int" ]
