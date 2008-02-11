

data List a
    = Nil
    | Cons a (List a)

-- a list is data, and exposes its constructors

cons = Cons  -- exposed
nil  = Nil   -- exposed

-- which, without laziness, only allows finite lists to be created.
-- it exposes the following destructor which guarantees halting.

listFold :: b                  -- nil case
         -> (a -> b -> b)      -- cons case
         -> (List a -> b)      -- resulting total function
listFold nf cf Nil = nf
listFold nf cf (Cons x xs) = cf x (listFold nf cf xs)

-- as an example, here is map defined for lists

listMap f = listFold nil (\x xs -> cons (f x) (listMap f xs))


data Stream a
    = Stream a (Stream a)

-- a stream is codata, and exposes its destructors

sHead (Stream a _)  = a   -- exposed
sTail (Stream _ as) = as  -- exposed

-- which only operate on infinite streams (sTail is total).  It 
-- exposes the following constructor which guarantees (lazy) 
-- destructibility.

                   -- (sHead case, sTail case)
streamUnfold :: (b -> (a         , b         )) 
             -> (b -> Stream a)  -- resulting total function
streamUnfold f x = let (a,b) = f x in Stream a (streamUnfold f b)

-- as an example, here is map defined for streams

streamMap f = streamUnfold (\s -> (f (sHead s), sTail s))
