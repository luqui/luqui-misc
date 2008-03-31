import System.IO
import System.Environment
import Data.Array

type Triangle a = Array (Int,Int) a

maxPath :: Triangle Integer -> Integer
maxPath tri = result ! (0,0)
    where
    result = array (bounds tri) (map maxPath' $ assocs tri)

    maxPath' ((r,c), n)
        | r >= fst (snd (bounds tri)) = ((r,c),n)
        | otherwise = ((r,c), n + max (result ! (r+1,c)) (result ! (r+1,c+1)))


makeTriangle :: String -> Triangle Integer
makeTriangle str = array ((0,0), (size-1,size-1)) triangle
    where 
    size = length (lines str)
    triangle = do
        (c, row) <- zip (lines str) [0..]
        (n, col) <- zip (words c) [0..]
        return $ ((row,col), read n)

main :: IO ()
main = do
    [filename] <- getArgs
    fh <- openFile filename ReadMode
    dat <- hGetContents fh
    let tri = makeTriangle dat
    print $ maxPath tri
