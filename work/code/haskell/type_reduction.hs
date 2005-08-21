data Type where
    Type    :: String -> Type
    Sup     :: Type -> Type -> Type
    Inf     :: Type -> Type -> Type
    Top     :: Type
    Bot     :: Type
    Bracket :: Type -> Type -> Type

instance Show Type

does :: Type -> Type -> Bool
does (Type a) (Type b) = does' a b
    where
    does' "Str" "Object" = True
    does' "Num" "Object" = True
    does' "Int" "Num"    = True
    does' "Int" "Object" = True
    does' _ _            = False

does (Sup a b) u = does a u && does b u
does t (Sup a b) = does t a || does t b
does (Inf a b) u = does a u || does b u
does t (Inf a b) = does t a && does t b
does _ Top       = True
does Top _       = False
does Bot _       = True
does _ Bot       = False
does (Bracket a b) u = does b u
does t (Bracket a b) = does t a

sup :: Type -> Type
sup (Bracket l r) = inf r
sup t             = t

inf :: Type -> Type
inf (Bracket l r) = sup l
inf t             = t

sup2 :: Type -> Type -> Type
sup2 a b = sup2' (sup a) (sup b)
    where
    sup2' x y
        | does x y  = y
        | does y x  = x
        | otherwise = Sup x y

inf2 :: Type -> Type -> Type
inf2 a b = inf2' (inf a) (inf b)
    where
    inf2' x y
        | does x y  = x
        | does y x  = y
        | otherwise = Inf x y

main :: IO ()
main = let 
         t = Bracket (Type "Int") (Type "Gobble")
         --u = Bracket t (Type "Num")
           in do
             print "T = ["
             print $ inf t
             print "|"
             --print $ sup t
             print "]"

             print "U = ["
             --print $ inf u
             print "|"
             --print $ sup u
             print "]"
