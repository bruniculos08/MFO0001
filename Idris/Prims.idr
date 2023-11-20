module Prims

x : Int
x = 94

foo : String
foo = "Sausage machine"

bar : Char
bar = 'Z'

quux : Bool
quux = False

-- No terminal:
--      Prims> 13 + 9*9
--      94
--      Prims> x == 13+9*9
--      True
--      Prims> x
--      94
--      Prims> if x == 8 * 8 + 30 then "Yes!" else "No!"
--      "Yes!"


app_one : a -> List a -> List a
app_one x [] = x :: Nil
app_one x (y :: xs) = x :: (y :: xs)
