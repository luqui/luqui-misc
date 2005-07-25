parent :: Sheep -> [Sheep]
parent a = maybeToList (mother a) `mplus` maybeToList (father a)

grandparent :: Sheep -> [Sheep]
grandparent a = parent a >>= parent
