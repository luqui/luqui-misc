{-# OPTIONS_GHC -fglasgow-exts #-}

import Control.Arrow hiding (pure)
import Control.Applicative
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Reader

import qualified Graphics.DrawingCombinators as D
import qualified Graphics.UI.SDL as SDL

type DTime = Double

type Drawing = D.Draw ()

data Behavior :: * -> * where
    Behavior :: s -> (DTime -> s -> (a,s)) -> Behavior a

instance Functor Behavior where
    fmap f (Behavior s0 step) = Behavior s0 (\dt -> first f . step dt)

instance Applicative Behavior where
    pure x = Behavior () (\dt _ -> (x,()))
    Behavior fs0 fstep <*> Behavior xs0 xstep = 
        Behavior (fs0,xs0) $ \dt (fs,xs) -> 
            let (f,fs') = fstep dt fs
                (x,xs') = xstep dt xs
            in (f x, (fs',xs'))


type Point = (Double,Double)

newtype Suspension t r m = Suspension { runSuspension :: forall x. t r m -> EventP t r m x }
newtype EventP t r m a = EventP { runEventP :: ReaderT (Suspension t r m) (ContT r m) a }

instance (Monad m) => Functor (EventP t r m) where
    fmap f (EventP m) = EventP $ fmap f m

instance (Monad m) => Monad (EventP t r m) where
    return = EventP . return
    EventP m >>= f = EventP (m >>= runEventP . f)

instance MonadTrans (EventP t r) where
    lift = EventP . lift . lift

instance (MonadIO m) => MonadIO (EventP t r m) where
    liftIO = EventP . liftIO


data SDLEvents r m = PrimEvents { sdlEventE :: SDL.Event -> EventP SDLEvents r m () }

sdlEvent :: (Monad m) => EventP SDLEvents r m SDL.Event
sdlEvent = EventP $ do
    callCC $ \cc -> do
        Suspension suspend <- ask
        runEventP $ suspend $ PrimEvents { sdlEventE = \p -> EventP (cc p) }


testProg :: (MonadIO m) => EventP SDLEvents r m Drawing
testProg = go (0,0)
    where
    go p = do
        e <- sdlEvent
        case e of
             SDL.MouseMotion x y _ _ -> go (fromIntegral x/320-1, fromIntegral y/240-1)
             SDL.MouseButtonDown _ _ _ -> return (D.translate p D.circle)
             _ -> go p


frpMain :: EventP SDLEvents Drawing IO Drawing -> IO ()
frpMain ev = do
    D.init
    SDL.init [SDL.InitVideo]
    SDL.setVideoMode 640 480 32 [SDL.OpenGL]

    drawing <- runContT (runReaderT (runEventP ev) (Suspension procEvents)) return
    D.draw drawing
    SDL.glSwapBuffers

    SDL.delay 2000

    where
    procEvents cbs = do
        e <- liftIO SDL.waitEvent
        sdlEventE cbs e
        return undefined

main = frpMain testProg
