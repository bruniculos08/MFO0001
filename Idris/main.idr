module Main

import Builtin

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
plus_reduce_other_side 0 = Refl
plus_reduce_other_side (S k) = cong S (plus_reduce_other_side k)

refl_comm : n = m -> m = n
refl_comm Refl = Refl

mult_zero : (n : Nat) -> 0 = mult n 0
mult_zero 0 = Refl
mult_zero (S k) = mult_zero k

plus_S_r : (n, m : Nat) -> plus n (S m) = S (plus n m)
plus_S_r 0 m = Refl
plus_S_r (S k) m = cong S (rewrite plus_S_r k m in cong S (Refl))

plus_comm : (n, m : Nat) -> plus n m = plus m n
plus_comm 0 m = plus_reduce_other_side m
plus_comm (S k) m = rewrite plus_S_r m k in cong S (rewrite plus_comm k m in Refl)
-- plus_comm (S k) m = rewrite plus_S_l m k in cong S (plus_comm k m)

plus_assoc : (n, m, o : Nat) -> plus n (plus m o) = plus m (plus n o) 
plus_assoc 0 m o = Refl
plus_assoc (S k) m o = rewrite plus_S_r m (plus k o) in cong S (rewrite plus_assoc k m o in Refl)

mult_S_r : (n, k : Nat) -> mult n (S k) = plus n (mult n k)
mult_S_r 0 k = Refl
mult_S_r (S j) k = cong S (rewrite mult_S_r j k in rewrite plus_assoc k j (mult j k) in Refl)

mult_comm : (n, m : Nat) -> mult m n = mult n m
mult_comm n 0 = rewrite refl_comm(mult_zero n) in Refl
mult_comm n (S k) = rewrite mult_S_r n k in rewrite mult_comm n k in Refl

summ_list : (List Nat) -> Nat
summ_list [] = 0
summ_list (x :: xs) = plus x (summ_list xs)

summ_to : Nat -> Nat
summ_to 0 = 0
summ_to (S k) = plus (S k) (summ_to k)

plus_1_S_l : (n : Nat) -> plus n 1 = S n
plus_1_S_l 0 = Refl
plus_1_S_l (S k) = rewrite plus_1_S_l k in Refl

plus_a_b_c_d : (a, b, c, d : Nat) -> (a + b) + (c + d) = (a + c) + (b + d)
plus_a_b_c_d 0 b c d = rewrite plus_assoc b c d in Refl
plus_a_b_c_d (S k) b c d = cong S (plus_a_b_c_d k b c d)

plus_a_b_c : (a, b, c : Nat) -> (a + b) + c = a + (b + c)
plus_a_b_c 0 b c = Refl
plus_a_b_c (S k) b c = cong S (plus_a_b_c k b c)

plus_1_S_r : (n : Nat) -> plus 1 n = S n
plus_1_S_r 0 = Refl
plus_1_S_r (S k) = cong S (plus_1_S_r k)
-- Aqui poderia se utilizar apenas Refl dessa maneira podemos como funciona a ideia de recursão...
-- ... que volta para o caso base

summ_form : (n : Nat) -> (n * (n + 1)) = (2 * summ_to n)
summ_form 0 = Refl
summ_form (S k) = cong S (rewrite mult_S_r k (plus k 1) 
    in (rewrite refl_comm (plus_reduce_other_side (plus k (summ_to k))) 
    in (rewrite summ_form k in (rewrite refl_comm (plus_reduce_other_side (summ_to k)) 
    in (rewrite plus_1_S_l k in (rewrite plus_S_r (plus k (summ_to k)) (plus k (summ_to k)) in 
    cong S (rewrite plus_a_b_c_d k (summ_to k) k (summ_to k) 
    in (rewrite plus_a_b_c k k (plus (summ_to k) (summ_to k)) in Refl))))))))

data MyTuple : Type -> Type -> Type where
    (@@) : a -> a -> MyTuple a a

infixr 10 @@;

distr : (a, b, c : Nat) -> a * (b + c) = a * b + a * c
distr 0 b c = Refl
distr (S k) b c = rewrite distr k b c in rewrite plus_a_b_c_d b c (mult k b) (mult k c) in Refl

data Nat_a = Z_a | S_a Nat_a

data Nat_b : Type where
    Z_b : Nat_b
    S_b : Nat_b -> Nat_b

-- data MyList a = MyNil | (.) a (MyList a)

map : (f : a -> a) -> List a -> List a
map f [] = []
map f (x :: xs) = ?map_rhs_1

even: Nat -> Bool
even 0 = True
even (S 0) = False
even (S (S k)) = even k

extract_first : (m : Nat ** p) -> m
extract_first ((fst ** snd)) = ?extract_first_rhs_0

mult_2_plus_twice : (n : Nat) -> 2 * n = n + n
mult_2_plus_twice 0 = Refl
mult_2_plus_twice (S k) = rewrite refl_comm(plus_reduce_other_side k) in Refl

even_mult_2 : (n : Nat) -> even n = True -> (m : Nat ** n = 2 * m)
even_mult_2 0 prf = (0 ** Refl)
even_mult_2 (S 0) prf = absurd prf
even_mult_2 (S (S k)) prf = (S (Builtin.DPair.DPair.fst (even_mult_2 k prf)) ** 
    rewrite refl_comm(plus_reduce_other_side (even_mult_2 k prf) .fst) in 
    rewrite (plus_S_r (even_mult_2 k prf).fst (even_mult_2 k prf).fst) in 
    rewrite refl_comm (mult_2_plus_twice (even_mult_2 k prf).fst) in 
    rewrite refl_comm(even_mult_2 k prf).snd in Refl)

fold : (f : a -> b -> b) -> b -> List a -> b
fold f x [] = x
fold f x (y :: ys) = f y (fold f x ys)

my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = fold count 0 (x :: xs) where
    count : a -> Nat -> Nat
    count n m = plus 1 m

my_app : List a -> List a -> List a
my_app [] ys = ys
my_app (x :: xs) ys = x :: (my_app xs ys)

partial fromMaybe : Maybe a -> Nat
fromMaybe (Just x) = 0
fromMaybe y = 1

data Le : Nat -> Nat -> Type where
   Le_n : (n : Nat) -> Le n n
   Le_S : (n, m : Nat) -> Le n m -> Le n (S m)

bigger_zero : (n : Nat) -> Le 0 n
bigger_zero 0 = Le_n 0
bigger_zero (S k) = Le_S 0 k (bigger_zero k)
