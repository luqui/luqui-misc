import Interface.TV.UI

applesU :: Input UI Int
applesU = iTitle "apples" (islider 3 (0,10))

bananasU :: Input UI Int
bananasU = iTitle "bananas" (islider 7 (0,10))

shoppingUO :: Output UI (Int -> Int -> Int)
shoppingUO = oTitle "shopping list" $ oLambda applesU (oLambda bananasU 0)
