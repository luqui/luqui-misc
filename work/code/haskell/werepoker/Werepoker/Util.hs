module Werepoker.Util
    ( getTime )
where

import qualified System.Time as Time

getTime :: IO Integer
getTime = do
    (Time.TOD sec _) <- Time.getClockTime
    return sec
