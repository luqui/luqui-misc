module Type (
    Type(..),  newType,
    Rule(..),
    Gut(..), 
) where
import Control.Monad
import Data.Unique


{-|
"gut f t" is a way to recursively perform a function
on homogeneous parts of a structure.  For instance,
for a Type t, "gut f t" replaces all the Types "u"
in the structure with "f u".
|-}
class Gut g where
    gut :: (MonadPlus m) => (g -> m g) -> g -> m g


------------------------------

data Type = Type String Unique
          | List Type
    deriving Ord

instance Eq Type where
    (Type _ ia) == (Type _ ib)  =  ia == ib
    (List t)    == (List u)     =  t == u
    _           == _            =  False

instance Show Type where
    show (Type name _) = name
    show (List t)      = "[" ++ show t ++ "]"

instance Gut Type where
    gut f (Type _ _)   = mzero
    gut f (List t)     = return . List =<< f t

newType :: String -> IO Type
newType name = newUnique >>= return . Type name

------------------------------

data Rule = Does Type Type
    deriving (Eq, Ord)

instance Show Rule where
    show (Does t u) = show t ++ " => " ++ show u
