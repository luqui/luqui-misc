import Fregl.SDL
import qualified Fregl.Drawing as Draw
import Fregl.Menu

main = runGameSDL $ \name -> do
    let (drawing, event) =
          menu name [ ("Start Game", return "start")
                    , ("Load Game", return "load")
                    , ("Options", return "options")
                    , ("Quit", return "quit")
                    ]

    fmap (fmap $ Draw.translate (0,5) . Draw.scale 4 4) $
        pure drawing `untilEvent` do
            item <- event
            return $ pure $ Draw.text item
