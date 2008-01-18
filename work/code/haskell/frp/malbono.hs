import Fregl.SDL
import qualified Fregl.Drawing as Draw
import qualified Malbono.Field as F

fieldB :: F.Field Double -> Ev (Signal (F.Field Double))
fieldB f = pure f `untilEvent` do
    dt <- waitTimestep
    fieldB $ F.balanceField viewFunc (1-dt) f

main = runGameSDL $ \_ -> do
    f <- fieldB (F.newField (64,48) (-16,-12) (33,25) 0)
    return $ F.drawField colorFunc <$> f

colorFunc v
    | v >= 0 = (10*v,0,0,1)
    | v <  0 = (0,0,-10*v,1)

viewFunc pos val = val + 1/(norm2 pos + 1)
