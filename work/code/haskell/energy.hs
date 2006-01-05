{-# OPTIONS_GHC -fglasgow-exts #-}

data Circuit where
    Series   :: Circuit -> Circuit -> Circuit
    Parallel :: Circuit -> Circuit -> Circuit
    Resistor :: Int                -> Circuit


reduce :: Circuit -> Int

reduce (Series x y)   = gcd (reduce x) (reduce y)
reduce (Parallel x y) = lcm (reduce x) (reduce y)
reduce (Resistor r)   = r

circuit :: Circuit
circuit = 
    Parallel
        (Series
            (Resistor 2)
            (Resistor 4))
        (Resistor 7)


main = print $ reduce circuit
