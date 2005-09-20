import qualified Data.Graph as Graph

data Type = Type String
          | Union Type Type
          | Intersection Type Type
          | Range Type Type
          | Bot
          | Top
    deriving Show

-- ugh, manual transitive closure for now
does_map "Object" "Object" = True
does_map "Str" "Str"    = True
does_map "Num" "Num"    = True
does_map "Int" "Int"    = True
does_map "Str" "Object" = True
does_map "Num" "Object" = True
does_map "Int" "Num"    = True
does_map "Int" "Object" = True
does_map _     _        = False

does :: Type -> Type -> Bool
does (Type a) (Type b) = does_map a b 
does (Range lo hi) t = does hi t
does t (Range lo hi) = does t lo
does (Union tx ty) u = (tx `does` u) && (ty `does` u)
does t (Union ux uy) = (t `does` ux) || (t `does` uy)
does (Intersection tx ty) u = (tx `does` u) || (ty `does` u)
does t (Intersection ux uy) = (t `does` ux) || (t `does` uy)
does _   Top = True
does Top _   = False
does Bot _   = True
does _   Bot = False
does _ _     = False

sup :: [Type] -> Type
sup [] = Bot
sup (a:as) 
    | a `does` sup as = sup as
    | sup as `does` a = a
    | otherwise       = Union a (sup as)

inf :: [Type] -> Type
inf [] = Top
inf (a:as)
    | a `does` inf as = a
    | inf as `does` a = inf as
    | otherwise       = Intersection a (inf as)

doescc :: Type -> Type -> [()]
doescc t u
    | does t u  = [()]
    | otherwise = []

doescv :: Type -> Type -> [Type]
doescv t r@(Range lo hi)
    | does t lo = [r]
    | does t hi = [Range t hi]
    | otherwise = []

doesvc :: Type -> Type -> [Type]
doesvc r@(Range lo hi) t
    | does hi t = [r]
    | does lo t = [Range lo t]
    | otherwise = []

doesvv :: Type -> Type -> [(Type, Type)]
doesvv r@(Range rlo rhi) s@(Range slo shi)
    | does rhi slo = [(r,s)]
    | does rhi shi && does slo rlo
        = [(r, Range rlo shi)]
    | does rhi shi && does rlo slo 
        = [(Range rlo slo, s), (r, Range rhi shi)]   -- backtracking :-(
    | otherwise = []

newvar :: Type
newvar = (Range Bot Top)

-- Int does T
-- T does U
-- U does T
-- T does Num

findme :: [Type]
findme = do
    t            <- doescv (Type "Int") newvar
    (t', u)      <- doesvv t newvar
    (u', t'')    <- doesvv u t'
    t'''         <- doesvc t'' (Type "Num")
    return t''

main :: IO ()
main = print findme
