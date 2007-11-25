import FRP

main :: IO ()
main = runFRP $ 
    zipB time (constB unitCircle) =>> \w ->
        translate (sin (fst (pull w)),cos (fst (pull w))) (snd (pull w))

