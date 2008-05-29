import qualified Text.ParserCombinators.Parsec as P
import Control.Monad
import qualified Data.Heap as Heap
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Writer

infixl 5 :@
data SK = S | K | SK :@ SK | Free
    deriving (Eq,Ord)

size :: SK -> Int
size (a :@ b) = size a + size b + 1
size _ = 1

showSK = go False
    where
    go parens S = "S"
    go parens K = "K"
    go parens Free = "?"
    go parens (a :@ b) = 
        let p = if parens then \s -> "(" ++ s ++ ")" else id
        in p (go False a ++ go True b)

parseSK str = case P.parse parseSeq "input" str of
                Left err -> error $ show err
                Right sk -> sk
    where
    parseSeq = liftM (foldl1 (:@)) $ P.many parseTerm 
    parseTerm = P.choice [ P.char 'S' >> return S
                         , P.char 'K' >> return K
                         , P.between (P.char '(') (P.char ')') parseSeq
                         ]

instance Show SK where
    show sk = "parseSK \"" ++ showSK sk ++ "\""

unify :: SK -> SK -> Maybe SK
unify Free x = Just x
unify x Free = Just x
unify S S = Just S
unify K K = Just K
unify (a :@ b) (a' :@ b') = liftM2 (:@) (unify a a') (unify b b')
unify _ _ = Nothing

unS (x :@ z :@ (y :@ z')) = 
    case unify z z' of
        Just z'' -> [S :@ x :@ y :@ z'']
        Nothing  -> []
unS _ = []

unK x = [K :@ x :@ Free]

step (S :@ x :@ y :@ z) = [x :@ z :@ (y :@ z)]
step (K :@ x :@ y)      = [x]
step _                  = []

combineTransforms :: [a -> [a]] -> a -> [a]
combineTransforms fs x = concatMap ($ x) fs

trans = combineTransforms [unS, unK, step]

transform :: (SK -> [SK]) -> SK -> [SK]
transform f x = f x ++ transform' x
    where
    transform' (a :@ b) = map (:@ b) (transform f a) ++ map (a :@) (transform f b)
    transform' _ = []


data MinSizePolicy

instance Heap.HeapPolicy MinSizePolicy SK where
    heapCompare _ x y = size x `compare` size y

search :: (SK -> [SK]) -> SK -> [SK]
search f sk = execWriter (evalStateT go ((Heap.singleton sk :: Heap.Heap MinSizePolicy SK), Set.empty))
    where
    extract = do
        (heap,set) <- get
        let (hd,heap') = Heap.extractHead heap
        if hd `Set.member` set
           then put (heap', set) >> extract
           else put (heap', Set.insert hd set) >> return hd
    go = do
        sk <- extract
        tell [sk]
        (heap,set) <- get
        put (foldr Heap.insert heap (transform f sk), set)
        go
