module Seminario

word : String
word = "Some string"

x, y : Int
x = 10
y = -5

value : Double
value = 0.25

letter : Char
letter = 'a'

flag : Bool
flag = False

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