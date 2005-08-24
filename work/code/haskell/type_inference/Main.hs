import Type
import Closure

main :: IO ()
main = sequence_ . map print . close =<< rules
    where
    rules = do
        a    <- newType "a"
        b    <- newType "b"
        gNum <- newType "Num"
        return [ Does a (List a),
                 Does (List $ List a) gNum,
                 Does b a ]
