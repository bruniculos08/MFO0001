Module integers.

Inductive bool :=
    | true
    | false.

Inductive nat :=
    | O
    | S(n : nat).

Fixpoint plus_natural(n m : nat) : nat :=
    match n with
    | O => m
    | S k => S(plus_natural k m)
    end.

Fixpoint minus_natural(a b : nat) : nat :=
    match a, b with
    | S n, S m => minus_natural n m
    | a, b => a
    end.

Fixpoint mult_natural(a b : nat) : nat :=
    match a with
    | O => O
    | S(n) => plus_natural (mult_natural n b) b
    end.

Fixpoint less_natural(a b : nat) : bool :=
    match a, b with
    | O, O => false
    | S n, O => false
    | O, S m => true
    | S n, S m => less_natural n m
    end.

Fixpoint div_natural(a b : nat) : nat :=
    match less_natural a b with
    | true => O
    | false => match a, b with
            | O, O => O
            | S n, O => O
            | O, S m => O
            | S n, S m => S (div_natural (minus_natural n m) (S m))
            end
    end.

Inductive int :=
    | Zero(O:nat)
    | Positive(n:nat)
    | Negative(n:nat).
    
End integers.