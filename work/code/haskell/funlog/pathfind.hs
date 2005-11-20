import Funlog.AST
import Funlog.Solve
import System.Environment

actClass  = Class {
                className = "Act",
                classCases = [
                    Case { 
                        caseName = "up",
                        caseSubs = [],
                        caseFun  = \ [] (IList [IInt x, IInt y]) -> IList [IInt x, IInt (y+1)]
                    },
                    Case { 
                        caseName = "down",
                        caseSubs = [],
                        caseFun  = \ [] (IList [IInt x, IInt y]) -> IList [IInt x, IInt (y-1)]
                    },
                    Case { 
                        caseName = "right",
                        caseSubs = [],
                        caseFun  = \ [] (IList [IInt x, IInt y]) -> IList [IInt (x+1), IInt y]
                    },
                    Case { 
                        caseName = "left",
                        caseSubs = [],
                        caseFun  = \ [] (IList [IInt x, IInt y]) -> IList [IInt (x-1), IInt y]
                    }
                ]
           }

actsClass = Class {
                className = "Acts",
                classCases = [
                    Case {
                        caseName = "comp",
                        caseSubs = [actClass, actsClass],
                        caseFun  = \ [a,as] -> as . a
                    },
                    Case {
                        caseName = "act",
                        caseSubs = [actClass],
                        caseFun  = \ [a] -> a
                    }
                ]
            }

main :: IO ()
main = do
    args <- getArgs
    let [x,y,x',y'] = map read args
    print $ head $ solve (IList [IInt x, IInt y]) (IList [IInt x', IInt y']) actsClass
