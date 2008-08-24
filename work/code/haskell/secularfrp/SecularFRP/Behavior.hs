module SecularFRP.Behavior 
    ( Behavior, stepper, switcher, unsafeDecomposeBehavior
    , Fun(..)
    )
where

import SecularFRP.Future
import SecularFRP.Event
import Control.Applicative hiding (Const)
import Control.Compose ((:.)(..))
import Data.Monoid

data Reactive a = a `Stepper` Event a

instance Functor Reactive where
    fmap f (a `Stepper` e) = f a `Stepper` fmap f e

instance Applicative Reactive where
    pure x = x `Stepper` mempty
    (f `Stepper` ef) <*> (x `Stepper` ex) = 
        f x `Stepper` 
            fmap (uncurry ($)) (iterateEvent (f,x) iterator)
        where
        iterator = fmap fside ef `mappend` fmap xside ex
        fside f' (cf,cx) = (f',cx)
        xside x' (cf,cx) = (cf,x')

data Fun a = Fun (Time -> a)
           | Const a

instance Functor Fun where
    fmap f (Fun t) = Fun (f . t)
    fmap f (Const a) = Const (f a)

instance Applicative Fun where
    pure = Const
    Const f <*> Const x = Const (f x)
    Const f <*> Fun xf  = Fun (const f <*> xf)
    Fun ff  <*> Const x = Fun (ff <*> const x)
    Fun ff  <*> Fun xf  = Fun (ff <*> xf)

newtype Behavior a = Behavior ((Reactive :. Fun) a)
    deriving (Functor,Applicative)

unBehavior (Behavior (O r)) = r

joinRE :: Event (Reactive a) -> Event a
joinRE e = do
    r `Stepper` re <- e
    return r `mappend` re

stepper :: a -> Event a -> Behavior a
stepper iv e = Behavior . O . fmap Const $ iv `Stepper` e

switcher :: Behavior a -> Event (Behavior a) -> Behavior a
switcher (Behavior (O (f `Stepper` ef))) eb = Behavior . O $
    f `Stepper` (ef `mappend` joinRE (fmap unBehavior eb))


unsafeDecomposeBehavior :: Behavior a -> (Fun a, Event (Fun a))
unsafeDecomposeBehavior (Behavior (O (r `Stepper` re))) = (r, re)
