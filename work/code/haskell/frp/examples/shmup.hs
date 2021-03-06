{-# OPTIONS -fglasgow-exts -farrows #-}

import Fregl.SDL
import qualified Fregl.Drawing as Draw
import System.Random

makeAvatar = 
    integral vzero $ 
        (10*^) <$> foldl (^+^) vzero 
               <$> liftList [ dir SDLK_w (0,1)
                            , dir SDLK_a (-1,0)
                            , dir SDLK_s (0,-1)
                            , dir SDLK_d (1,0)
                            ]
    where
    dir k d = (\down -> if down then d else vzero) <$> keyState k

makeBullet src dest = 
    integral src (pure dir)
    where
    dir = 20 *^ normalize (dest ^-^ src)

fireBullets avatar = pure [] `untilEvent` do
    pos <- waitClickPos ButtonLeft MouseDown
    av <- readSig avatar
    bullet <- makeBullet av pos
    rest <- fireBullets avatar
    liftA2 (:) bullet rest `untilEvent` do
        bpos <- readSig bullet
        when (not . inRange <$> bullet)
        return rest
    where
    inRange (x,y) = -13 < x && x < 13
                 && -10 < y && y < 10

drawAvatar pos = Draw.translate pos Draw.circle

drawBullet pos = Draw.translate pos $ Draw.scale 0.1 0.1 Draw.circle

drawEnemy phase pos = Draw.color (1,0,0,1)
                    $ Draw.translate pos 
                    $ Draw.scale 0.5 0.5 
                    $ Draw.regularPoly $ floor (8 * abs (sin phase)+1)

makeEnemy initialPos avatar = mdo
    x <- integral initialPos =<< integral (0,0) (liftA2 dir x avatar)
    return x
    where
    dir self avatar = normalize (avatar ^-^ self)

makeEnemies :: [Vec2] -> Signal Vec2 -> Signal [Vec2] -> Ev (Signal [Vec2])
makeEnemies [] _ _ = return $ pure []
makeEnemies (r:rs) avatar bullets = pure [] `untilEvent` do
    delay 2
    enemy <- makeEnemy r avatar
    rest <- makeEnemies rs avatar bullets
    liftA2 (:) enemy rest `untilEvent` do
        when (liftA2 testHit enemy bullets) 
            `mappend` when (liftA (not . inRange) enemy)
        return rest
    where
    testHit enemy bullets = any (hit enemy) bullets
    hit enemy bullet = norm (enemy ^-^ bullet) < 0.6
    inRange (x,y) = x > -16 && x < 16 && y > -12 && y < 12

main = runGameSDL $ \_ -> do
    let rands = randomRs ((-16,-12),(16,12)) $ mkStdGen 42
    fromSF $ proc () -> do
        avatar  <- sf_ makeAvatar  -< ()
        bullets <- sf fireBullets -< avatar
        enemies <- sf (sfUncurry2 $ makeEnemies rands) -< (avatar,bullets)
        t <- sf_ $ time -< ()
        let bulletDrawings = mconcat (map drawBullet bullets)
        let enemyDrawings = mconcat (map (drawEnemy t) enemies)
        returnA -< mconcat [drawAvatar avatar, bulletDrawings, enemyDrawings]



-- functions that should be in the library

liftList :: (Applicative f) => [f a] -> f [a]
liftList [] = pure []
liftList (x:xs) = liftA2 (:) x (liftList xs)

instance Random Vec2 where
    random g = let (x,g') = random g
                   (y,g'') = random g'
               in ((x,y),g'')
    randomR ((minx,miny),(maxx,maxy)) g =
        let (x,g') = randomR (minx,maxx) g
            (y,g'') = randomR (miny,maxy) g'
        in ((x,y),g'')

sfUncurry2 :: (Signal a -> Signal b -> Ev (Signal c)) -> (Signal (a,b) -> Ev (Signal c))
sfUncurry2 f = uncurry f . (fmap fst &&& fmap snd)
