import qualified Graphics.UI.SDL as SDL

class (Functor w) => Comonad w where
    (=>>) :: w a -> (w a -> b) -> w b
    x =>> f = fmap f (cojoin x)

    coreturn :: w a -> a
    cojoin :: w a -> w (w a)

data CA a = CA [a] a [a]

moveLeft,moveRight :: CA a -> CA a
moveLeft  (CA (prev:prevs) here nexts) = CA prevs prev (here:nexts)
moveRight (CA prevs here (next:nexts)) = CA (here:prevs) next nexts

instance Functor CA where
    fmap f (CA prevs here nexts) = CA (map f prevs) (f here) (map f nexts)

instance Comonad CA where
    coreturn (CA _ x _) = x
    cojoin x = CA (tail $ iterate moveLeft x) x (tail $ iterate moveRight x)


newtype CA2 a = CA2 (CA (CA a))

instance Functor CA2 where
    fmap f (CA2 x) = CA2 $ fmap (fmap f) x

instance Comonad CA2 where
    coreturn (CA2 x) = coreturn . coreturn $ x
    cojoin (CA2 x) = fmap CA2 $ CA2 $ roll $ roll x
        where
        iterate1 f = tail . iterate f
        roll a = CA (iterate1 (fmap moveLeft) a) a (iterate1 (fmap moveRight) a)

runCA :: (Comonad m) => (m a -> a) -> m a -> [m a]
runCA f = iterate (=>> f)

------------------  That was the kernel, now for silly UI stuff -----------

rule110 :: CA Bool -> Bool
rule110 (CA (a:_) b (c:_)) = not ( and [    a,    b,    c]
                                || and [    a,not b,not c]
                                || and [not a,not b,not c]
                                 )

ruleConway :: CA2 Bool -> Bool
ruleConway (CA2 (CA 
    ((CA (a:_) b (c:_)):_)
     (CA (d:_) e (f:_))
    ((CA (g:_) h (i:_)):_))) = 
        let n = length $ filter id [a,b,c,d,  f,g,h,i] in
        if e
            then n == 2 || n == 3
            else n == 3

showLine :: Int -> CA Bool -> String
showLine cxt (CA as b cs) = 
        map toch (reverse (take cxt as) ++ [b] ++ take cxt cs) 
    where
    toch True  = 'x'
    toch False = ' '

showCA2 :: Int -> CA2 Bool -> String
showCA2 cxt (CA2 (CA as b cs)) = 
    unlines $ map (showLine cxt) (reverse (take cxt as) ++ [b] ++ take cxt cs)

cfgToCA2 :: [[Int]] -> CA2 Bool
cfgToCA2 xss = CA2 $ CA (cfgToCA2' [])
                        (CA (repeat False) False (repeat False))
                        (cfgToCA2' xss)
    where
    cfgToCA2' []       = repeat $ CA (repeat False) False (repeat False)
    cfgToCA2' ([]:xss) = CA (repeat False) False (repeat False):cfgToCA2' xss
    cfgToCA2' (xs:xss) = 
        CA (repeat False) False (map (/= 0) xs ++ repeat False):cfgToCA2' xss

main :: IO ()
main = do
    let ca = cfgToCA2 [[0,1,0]
                      ,[0,0,1]
                      ,[1,1,1]]
    mapM_ (putBoard . showCA2 10) $ runCA ruleConway ca
    where
    putBoard x = do
        putStr $ x ++ "--\n"
        getLine
