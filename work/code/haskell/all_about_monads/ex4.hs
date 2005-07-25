maybeM :: (MonadPlus m) => Maybe a -> m a
maybeM Nothing  = mzero
maybeM (Just a) = return a

parent :: (MonadPlus m) => Sheep -> m Sheep
parent a = maybeM (mother a) `mplus` maybeM (father a)

grandparent :: (MonadPlus m) => Sheep -> m Sheep
grandparent a = (maybeM (mother a) >>= parent) `mplus` 
                (maybeM (father a) >>= parent)
