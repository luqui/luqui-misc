import Data.List
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Writer
import qualified Text.ParserCombinators.ReadP as P
import System.Environment

infixl 9 :*

data Term
    = S | K | Term :* Term
    deriving (Eq,Ord)

instance Show Term where show = showTerm False

showTerm :: Bool -> Term -> String
showTerm p S = "S"
showTerm p K = "K"
showTerm p (a :* b) = mparens (showTerm False a ++ showTerm True b)
    where
    mparens s | p         = "(" ++ s ++ ")"
              | otherwise = s

encodeTerm :: Term -> String
encodeTerm S = "S"
encodeTerm K = "K"
encodeTerm (a :* b) = "x" ++ encodeTerm a ++ encodeTerm b

rewrite :: Term -> [Term]
rewrite t = sred t ++ kred t ++ sexp t ++ kexp t
    where
    sred (S :* x :* y :* z) = [x :* z :* (y :* z)]
    sred _ = []
    kred (K :* x :* y)      = [x]
    kred _ = []
    sexp (x :* z :* (y :* z')) | z == z' = [S :* x :* y :* z]
    sexp _ = []
    kexp x = [K :* x :* S, K :* x :* K]
    
traverse :: (Term -> [Term]) -> Term -> [Term]
traverse f S = f S
traverse f K = f K
traverse f (a :* b) = f (a :* b) 
                   ++ map (:* b) (traverse f a) 
                   ++ map (a :*) (traverse f b)

infix 8 :->
data Edge = Term :-> Term
    deriving Show

instance Eq Edge where
    (a :-> b) == (c :-> d) = (a == c && b == d) || (a == d && b == c)

showEdge :: Edge -> String
showEdge (a :-> b) = encodeTerm a ++ " -- " ++ encodeTerm b

data TermOrd = TermOrd Int Term
    deriving (Eq,Ord)

mkTermOrd t = TermOrd (size t) t
    where
    size S = 1
    size K = 1
    size (a :* b) = 1 + size a + size b

unless' z True  m = return z
unless' z False m = m

mkGraphM :: Set.Set TermOrd -> WriterT [Edge] (State (Set.Set Term)) ()
mkGraphM terms = do
    case Set.minView terms of
        Nothing -> return ()
        Just (TermOrd _ term, rest) -> do
            seen <- gets (term `Set.member`)
            new <- unless' Set.empty seen $ do
                let next = traverse rewrite term
                tell $ map (term :->) next
                modify (Set.insert term)
                return (Set.fromList . map mkTermOrd $ next)
            mkGraphM (rest `Set.union` new)

mkGraph :: [Term] -> [Edge]
mkGraph ts = evalState (execWriterT (mkGraphM . Set.fromList . map mkTermOrd $ ts)) Set.empty

interior :: [Edge] -> [Edge]
interior es = filter (\(n1 :-> n2) -> interesting n1 && interesting n2) es
    where
    interesting n = 
        case [ () | (n1 :-> n2) <- es, n1 == n || n2 == n ] of
            _:_:_ -> True
            _     -> False

mkGraphFile :: Int -> Term -> String
mkGraphFile size t = 
    "graph sk {\n" ++
    "node [fontsize=8, width=0, height=0]\n" ++
    "nslimit=10;\n" ++
    (intercalate ";\n" . map showEdge . interior . take size . nub . mkGraph $ [t])
    ++ ";\n}\n"


readSK :: P.ReadP Term
readSK = fmap (foldl1 (:*)) (P.many1 readTerm)
    where
    readTerm = P.choice [
        P.char 'S' >> return S,
        P.char 'K' >> return K,
        do { P.char '('; x <- readSK; P.char ')'; return x }
      ] 

main = do
    [depthS, termS] <- getArgs
    let depth = read depthS
    let (term:_) = [ r | (r,"") <- P.readP_to_S readSK termS ]
    putStr $ mkGraphFile depth term
