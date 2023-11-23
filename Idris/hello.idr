module Main

main : IO ()
main = putStrLn "Hello world"

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
plus_comm (S k) m = rewrite plus_S_r m k in 
    rewrite plus_comm m k in ?plus_comm_rhs_1
-- plus_comm 0 m = plus_reduce_other_side m
-- plus_comm (S k) m = rewrite plus_S_r m k in cong S (rewrite plus_comm k m in Refl)