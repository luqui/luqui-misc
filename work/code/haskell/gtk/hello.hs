import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

closeButtonHandler :: GladeXML -> IO ()
closeButtonHandler xml = do
    window <- xmlGetWidget xml castToWindow "window1"
    closeButton <- xmlGetWidget xml castToButton "button2"
    onClicked closeButton $ do
        widgetDestroy window
    return ()

applyAction :: GladeXML -> IO (IO ())
applyAction xml = do
    label <- xmlGetWidget xml castToLabel "label1"
    entry <- xmlGetWidget xml castToEntry "entry1"
    return $ do
        name <- get entry entryText
        set label [ labelText := "Hello, " ++ name ]

applyButtonHandler :: GladeXML -> IO ()
applyButtonHandler xml = do
    applyButton <- xmlGetWidget xml castToButton "button1"
    action <- applyAction xml
    onClicked applyButton action
    return ()

entryHandler :: GladeXML -> IO ()
entryHandler xml = do
    entry <- xmlGetWidget xml castToEntry "entry1"
    action <- applyAction xml
    onEntryActivate entry action
    return ()



initializers :: [GladeXML -> IO ()]
initializers = [ closeButtonHandler, applyButtonHandler, entryHandler ]

main :: IO ()
main = do
    initGUI
    Just xml <- xmlNew "hello.glade"
    window <- xmlGetWidget xml castToWindow "window1"
    onDestroy window mainQuit
    sequence $ map ($ xml) initializers
    widgetShowAll window
    mainGUI
