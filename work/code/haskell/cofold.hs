

data List a
    = Nil
    | Cons a (List a)

-- a list is data, and exposes its constructors

cons = Cons  -- exposed
nil  = Nil   -- exposed

-- which, without laziness, only allows finite lists to be created.
-- it exposes the following destructor which guarantees halting.

listFold :: b                  -- nil case
         -> (a -> List a -> b) -- cons case
         -> List a             -- object
         -> b
listFold nf cf Nil = nf
listFold nf cf (Cons x xs) = cf x xs

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

streamFold :: (a -> b)        -- sHead case
           -> (a -> Stream b) -- sTail case
           -> a
           -> Stream b
streamFold hf tf x = Stream (hf x) (tf x)

-- as an example, here is map defined for streams

streamMap f = streamFold (f . sHead) (streamMap f . sTail)
