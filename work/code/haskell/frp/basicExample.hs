import Fregl.Event
import Fregl.Signal
import Control.Applicative

data EV
    = TimestepEvent Double
    | MouseClickEvent (Double,Double)

waitTimestep :: Event EV Double
waitTimestep = do
    ev <- waitEvent
    case ev of
         TimestepEvent dt -> return dt
         _                -> waitTimestep

waitClick :: Event EV (Double, Double)
waitClick = do
    ev <- waitEvent
    case ev of
         MouseClickEvent pos -> return pos
         _                   -> waitClick

time :: Behavior EV Double
time = time' 0
    where
    time' init = 
        pure init 
          `untilEvent` 
            (waitTimestep >>= bindBehavior . time' . (+init))

rising :: Behavior EV Double
rising = time `untilEvent` (waitClick >> bindBehavior rising)

testProg :: Behavior EV Double
testProg = rising

main = do
    cxt <- newEventCxt testProg
    runMain cxt
    where
    runMain cxt = do
        print (readEventCxt cxt)
        estring <- getLine
        let e' = case estring of
                "t" -> TimestepEvent 0.1
                "c" -> MouseClickEvent (0,0)
                _   -> TimestepEvent 0
        runMain =<< nextEventCxt e' cxt
