import FRP

main :: IO ()
main = runFRP $ fmap (\x' -> translate x' $ unitCircle) mousePos
