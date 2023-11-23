module Test

average : Double -> Double -> Double
average x y = (x + y)/2

infixr 10 :::

data Bin = Zero | Um

data Vect_main : Nat -> Type -> Type where
    Nil_main : Vect_main Z a
    (:::) : a -> Vect_main k a -> Vect_main (S k) a


app_one : a -> Vect_main k a -> Vect_main (S k) a
app_one j x = (:::) j x

-- Lembre-se do erro se utilizarmos 'Vect_main (S k) a' como retorno:
app_two : a -> a -> Vect_main k a -> Vect_main (S (S k)) a
app_two x y xs = x ::: (y ::: xs)

app_vect : Vect_main m a -> Vect_main n a -> Vect_main (m + n) a
app_vect Nil_main y = y
app_vect (x ::: z) y = x ::: (app_vect z y)