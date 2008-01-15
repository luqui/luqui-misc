{-# OPTIONS_GHC -fglasgow-exts #-}

module Fregl.Menu where

import Fregl.Core
import Fregl.Splittable
import Fregl.Event
import Data.Monoid
import qualified Fregl.Drawing as Draw

menu :: forall v a. (EventVal v) 
     => Draw.Name  -- a supply of drawing names
     -> [ (String, Event v a) ] -- the menu items
     -> (Draw.Drawing, Event v a)
menu name items =

    let (drawings, events) = 
          unzip $ zipWith3 makeItem (names name) [0..] items
    in (mconcat drawings, firstOfEvents events)

    where
    
    makeItem :: Draw.Name -> Int -> (String, Event v a)
             -> (Draw.Drawing, Event v a)
    makeItem name pos (text,ev) = 
        ( menuItem name pos text
        , waitClickName ButtonLeft MouseDown name >> ev
        )

    menuItem :: Draw.Name -> Int -> String
             -> Draw.Drawing
    menuItem name pos text =
        Draw.translate (0, -fromIntegral pos)
            $ Draw.name name
            $ Draw.text text

    names :: Draw.Name -> [Draw.Name]
    names name = 
        let (n,n') = split name
        in n : names n'
