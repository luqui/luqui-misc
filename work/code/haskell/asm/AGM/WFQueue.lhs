> module AGM.WFQueue
>     ( TWriter, TFollower
>     , newWFQueue, readFollower, nextFollower, appendWriter
>     )
> where
> 
> import Control.Concurrent.STM
> import Control.Applicative ((<$>))

A writer-follower queue is basially a linked list with two interfaces, a
writer and a follower.  The writer is a mutable interface that can
append to the end of the linked list; the follower is a immutable
interface that represents a nonempty cell of the list.  The follower
can get the current value or get the follower for the next cell.

Note that a writer-follower queue is always non-empty, because the
writer always has to refer to a non-empty cell.

> data TFollower a 
>     = TFollower { readFollower :: a
>                 , nextFollower :: STM (Maybe (TFollower a))
>                 }
> newtype TWriter a 
>     = TWriter { appendWriter :: a -> STM () }
> 
> newWFQueue :: a -> STM (TWriter a, TFollower a)
> newWFQueue init = do
>     cdr <- newTVar Nothing
>     let follower = TFollower init (readTVar cdr)
>     curWriter <- newTVar cdr
>     let writer = TWriter $ \x -> do
>             cell <- readTVar curWriter
>             next <- newTVar Nothing
>             writeTVar cell $ Just $ TFollower x (readTVar next)
>             writeTVar curWriter next
>     return (writer, follower)
> 
> instance Functor TFollower where
>     fmap f (TFollower car cdr) = 
>         TFollower (f car) (fmap (fmap (fmap f)) cdr)

vim: tw=72
