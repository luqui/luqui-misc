parent :: Sheep -> Maybe Sheep
parent a = mother a `mplus` father a

grandparent :: Sheep -> Maybe Sheep
grandparent = (mother s >>= parent) `mplus` (father s >>= parent)
