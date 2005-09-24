import Data.List

data Case a = Case { input :: [a], output :: [a] }
    deriving Show
data Role a = Role { cases :: [Case a] }
    deriving Show
data Node a = Node { name :: String }
    deriving Show
data Link a = Link { left :: Node a, right :: Node a, kind :: a }
    deriving Show
data OpenLink a = OpenLink { node :: Node a, openKind :: a }
    deriving Show
data LinkState a = LinkState { open :: [OpenLink a], closed :: [Link a] }
    deriving Show

bind :: (Eq a) => Node a -> Role a -> LinkState a -> [LinkState a]
bind node' role state = do
    c <- cases role
    if input c `isPrefixOf` map openKind (open state)
        then [ LinkState { 
                    open = openLinks node' (output c) ++ drop (length $ input c) (open state),
                    closed = closeLinks node' (open state) ++ closed state } ]
        else []
    where
    openLinks :: Node a -> [a] -> [OpenLink a]
    openLinks node' kinds = map (\k -> OpenLink { node = node', openKind = k }) kinds
    
    closeLinks :: Node a -> [OpenLink a] -> [Link a]
    closeLinks node' opens = 
        map (\op -> Link { left = node op, right = node', kind = openKind op }) opens

------------------------------

makeRole "^"    = Role [ Case [] [ "^" ] ]

makeRole "$"    = Role [ Case [ "$" ] [] ]

makeRole "verb" = Role [ Case [ "actor", "^" ] [ "$" ],
                         Case [ "actor", "^" ] [ "object", "$" ] ]

makeRole "noun" = Role [ Case [] [ "actor" ],
                         Case [ "object" ] [] ]

makeRole x      = error $ "Unknown role: " ++ x

getRole "^"      = makeRole "^"
getRole "$"      = makeRole "$"
getRole "dog"    = makeRole "noun"
getRole "cat"    = makeRole "noun"
getRole "chases" = makeRole "verb"
getRole x        = error $ "Unknown term: " ++ x


initState = [LinkState { open = [], closed = [] }]

vBind :: String -> LinkState String -> [LinkState String]
vBind word = bind (Node word) (getRole word)

vParse :: String -> [LinkState String]
vParse s = foldl (>>=) initState $ map vBind (words s)
