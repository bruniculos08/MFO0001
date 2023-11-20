module Main

-- Data Types:
data Nat_main = Z_main | S_main Nat_main

data List_main : Type -> Type where 
    Nil_main : List_main a
    (::) : a -> List_main a -> List_main a

-- Forma de pensar sobre o tipo vetor: ele se tiver um natural e um elemento de um tipo forma um tipo
data Vect_main : Nat_main -> Type -> Type where
    Nil_main_vect : Vect_main Z_main a
    (:::) : a -> Vect_main k a -> Vect_main (S_main k) a

-- S e :: são operadores, 'a' é um tipo (definição polimorfica)
-- O construtor (::) recebe um elemento do tipo 'a' e uma lista do tipo 'a'
-- A seguir se define a order de precedência do operador:
infixr 10 ::
infixr 10 :::
-- Obs.: o operador é infixo mas como foi defindo com parentes ele pode ser usado de maneira...
-- ... pré-fixa se usado entre parenteses.

-- Functions:

-- Unary addition
plus' : Nat_main -> Nat_main -> Nat_main
plus' Z_main y = y
plus' (S_main n) y = S_main (plus' n y)

-- Unary multiplication
mult' : Nat_main -> Nat_main -> Nat_main
mult' Z_main y = y
mult' (S_main n) y = plus' y (mult' n y)

-- No terminal:
--      Main> plus (S (S Z)) (S (S Z))
--      4
--      Main> mult (S (S (S Z))) (plus (S (S Z)) (S (S Z)))
--      12

-- Reverse list (using auxiliary function revAcc'):
reverse' : List_main a -> List_main a
reverse' xs = revAcc' Nil_main xs where
    revAcc' : List_main a -> List_main a -> List_main a
    revAcc' acc Nil_main = acc
    revAcc' acc (x :: xs) = revAcc' (x :: acc) xs

map_main : (Nat -> Nat) -> List Nat -> List Nat
map_main f Nil = Nil
map_main f (x :: xs) = (f x) :: (map f xs) 

-- vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c

plus_reduce : (n : Nat) -> n = plus Z n
plus_reduce n = Refl

plus_reduce_other_side : (n : Nat) -> n = plus n Z
plus_reduce_other_side 0 = ?plus_reduce_other_side_rhs_0
plus_reduce_other_side (S k) = cong S (plus_reduce_other_side k)

refl_comm : n = m -> m = n
refl_comm Refl = Refl

mult_zero : (n : Nat) -> 0 = mult n 0
mult_zero 0 = Refl
mult_zero (S k) = mult_zero k

plus_comm : (n : Nat) -> (m : Nat) -> plus n m = plus m n
plus_comm 0 0 = Refl
plus_comm 0 (S k) = cong S (plus_reduce_other_side k)
plus_comm (S k) 0 = refl_comm (cong S (plus_reduce_other_side k))
plus_comm (S k) (S j) = ?plus_comm_rhs_5
