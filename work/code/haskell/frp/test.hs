import FRP

main :: IO ()
main = runFRP $ constB unitCircle
