Module tutorial.
From Coq Require Import Unicode.Utf8.

Inductive bool :=
    |true
    |false.
Check true.

Definition andb(a b: bool): bool := 
    match a with 
    |false => false
    |true => b
    end.

Compute andb true true.

Definition orb(a b: bool): bool :=
    match a with
    |true => true
    |false => b
    end.

Compute orb true false.

Definition notb(a : bool): bool :=
    match a with
    |true => false
    |false => true
    end.

Definition implieb(a b : bool): bool :=
    match a with
    | false => true
    | true => b
    end.

Example and_example: andb true false = false.
Proof.
    simpl. reflexivity.
Qed.

(*Comentários*)
Theorem imp_eq: forall (a b : bool),
    (implieb a b) = (orb (notb a) b).
Proof.
    intros.
    destruct a; destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.   
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem imp_eq_prop: forall (A B: Prop),
(~A \/ B) -> A -> B.
Proof.
    intros  A B. intro.
    intro. destruct H as [H1 | H2].
    - unfold not in H1. apply H1 in H0 as H3. destruct H3.
    - apply H2.
Qed.

Theorem dem: forall A B: Prop,
    ~(A \/ B) <-> ~A /\ ~B.
Proof.
    intros A B. split.
    - intro. split.
        + unfold not. intro. unfold not in H. 
        apply H. left. apply H0.
        + intro. apply H. right; apply H0.
    - intro. unfold not. intro. destruct H. destruct H0.
        + unfold not in H. apply H in H0. apply H0.
        + unfold not in H1. apply H1 in H0. apply H0.
Qed.

Theorem dem2: forall A B: Prop,
    ~A \/ ~B -> ~(A /\ B).
Proof.
    intros A B. intro. unfold not. intro. destruct H0. destruct H.
        + unfold not in H. apply H in H0. apply H0.
        + unfold not in H. apply H in H1. apply H1.
Qed.

Inductive nat :=
    |O
    |S(n:nat).

Fixpoint even (a : nat) : bool :=
    match a with 
    | O => true
    | S O => false
    | S(S n) => even n
    end.

Fixpoint sum(a b : nat) : nat :=
    match a with
    | O => b
    | S(n) => S(sum n b)
    end.

Compute sum (S O) (S O).

Theorem dem3: forall a: nat,
    sum O a = a.
Proof.
    intro. simpl. reflexivity.
Qed.

Theorem dem4: forall a: nat,
    sum a O = a.
Proof.
    induction a as [| H].
    - simpl. reflexivity.
    - simpl. rewrite IHH. reflexivity.
Qed.

Fixpoint mult(a b : nat) : nat :=
    match a with
    | O => O
    | S(n) => sum (mult n b) b
    end.

Compute mult (S (S O)) (S (S (S O))).

Fixpoint sub(a b : nat) : nat :=
    match a, b with
    | S n, S m => sub n m
    | a, b => a
    end.

Compute sub (S O)  O.
Compute sub O  (S O).

Fixpoint lessEq(a b : nat) : bool :=
    match a, b with
    | O, O => true
    | O, S m => true
    | S n, O => false
    | S n, S m => lessEq n m
    end.

Fixpoint less(a b : nat) : bool :=
    match a, b with
    | O, O => false
    | S n, O => false
    | O, S m => true
    | S n, S m => less n m
    end.

Fixpoint mod(a b : nat) : nat :=
    match a, b with
    | O, O => O
    | S n, O => a
    | O, S m => O
    | S n, S m => mod n m
    end.

Fixpoint pred(a : nat) : nat :=
    match a with
    | O => O
    | S n => n
    end.

Fixpoint div(a b : nat) : nat :=
    match less a b with
    | true => O
    | false => match a, b with
            | O, O => O
            | n, S O => n
            | S n, O => O
            | O, S m => O
            | S n, S m => S (div (sub n m) (S m))
            end
    end.

Compute div (S(S O)) (S(S O)).

Lemma aux_com_sum: forall a b: nat,
    sum a (S b) = S (sum a b).
Proof.
    intros. induction a as [| H].
    - simpl. reflexivity.
    - simpl. rewrite IHH. reflexivity.
Qed.

Theorem comutativity_sum: forall a b : nat, 
    sum a b = sum b a.
Proof.
    intros. induction a as [| H].
    - simpl. rewrite dem4. reflexivity.
    - simpl. rewrite IHH. rewrite aux_com_sum. reflexivity.
Qed.

Fixpoint xorb(a b : bool) : bool :=
    match a, b with
    | false, false => false
    | true, true => false
    | true, false => true
    | false, true => true
    end.

Fixpoint odd(a : nat) : bool :=
    match a with
    | O => false
    | S O => true
    | S(S n) => odd n
    end.

Lemma associatividade_sum: forall a b c : nat,
    sum a (sum b c) = sum c (sum b a).
Proof.
    intros. induction a as [|k].
    - simpl. symmetry. rewrite comutativity_sum.
        rewrite dem4. reflexivity.
    - simpl. symmetry. rewrite comutativity_sum. 
        rewrite (comutativity_sum b (S k)). simpl (sum (S k) b).
        simpl. symmetry. rewrite IHk.
        rewrite (comutativity_sum b k).
        rewrite (comutativity_sum c (sum k b)).
        reflexivity. 
Qed.

Lemma mult_por_zero: forall b : nat,
    mult O b = mult b O.
Proof.
    intros. induction b as [| H].
    - simpl. reflexivity.
    - simpl. rewrite comutativity_sum. simpl. simpl in IHH. apply IHH. 
Qed.

Lemma mult_por_um_right: forall b : nat,
    mult b (S O) = b.
Proof.
    intros. induction b as [| H].
    - simpl. reflexivity.
    - simpl. rewrite IHH. rewrite comutativity_sum. simpl. reflexivity.
Qed.

Lemma mult_por_um_left: forall b : nat,
    mult (S O) b = b.
Proof.
    intros. induction b as [| H].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma mult_k_mais_um: forall a b : nat, 
    mult a (S b) = sum (mult a b) a.
Proof.
    intros. induction a as [| H].
    - simpl. reflexivity.
    - symmetry. simpl. rewrite IHH. rewrite comutativity_sum.
        symmetry. rewrite comutativity_sum. simpl.
        rewrite (associatividade_sum b (mult H b) H).
        reflexivity.
Qed.

Theorem comutativity_mult: forall a b : nat,
    mult a b = mult b a.
Proof.
    intros. induction a as [| k].
    - rewrite mult_por_zero. reflexivity.
    - simpl. rewrite IHk. symmetry. rewrite mult_k_mais_um.
        reflexivity.
Qed.

Notation "a + b" := (sum a b).
Notation "a - b" := (sub a b).
Notation "a * b" := (mult a b).
Notation "a / b" := (div a b).

Fixpoint power(a b : nat) : nat :=
    match a, b with
    | a, O => S O
    | O, b => O
    | S O, b => S O
    | a, S m => mult a (power a m)
    end. 

Theorem contra_pos: forall p q : Prop,
    (p -> q) -> (~q -> ~p) .
Proof.
    intros. intro. apply H in H1. apply H0 in H1.
    apply H1.
Qed.

Theorem neg_diff_true: forall a : bool,
    (a <> true) -> (a = false).
Proof.
    intros a. destruct a.
    + intros. destruct H. reflexivity.
    + intros. reflexivity. 
Qed.

Theorem neg_diff_false: forall a : bool,
    (a <> false) -> (a = true).
Proof.
    intros a. destruct a.
    + intros. reflexivity.
    + intros. destruct H. reflexivity.
Qed.

Theorem not_even_then_false: forall a : nat,
    (even a <> true) -> (even a = false).
Proof.
    intro. intro. pose (neg_diff_true) as ident.
    apply ident in H. apply H.
Qed.

Theorem even_then_true: forall a : nat,
    (even a <> false) -> (even a = true).
Proof.
    intro. intro. pose (neg_diff_false) as ident.
    apply ident in H. apply H.
Qed.

Theorem true_then_not_false: forall a: bool,
    (a = true) -> (a <> false).
Proof.
    intros. destruct a.
    - discriminate.
    - contradict H. discriminate.    
Qed.

Theorem succ_not_even: forall a : nat,
    (even a = true) -> (even (S a) = false).
Proof.
    intros. induction a as [| k].
    - simpl. reflexivity.
    - simpl. apply contra_pos in IHk.
        + apply not_even_then_false in IHk. apply IHk. 
        + apply true_then_not_false in H. apply H. 
Qed.

Lemma mult_per_zero_right: forall a : nat,
    a * O = O.
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - simpl. rewrite dem4. apply IHk.
Qed.

Lemma mult_per_zero_left: forall a : nat,
    O * a = O.
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma div_zero: forall n : nat,
    n <> O -> O / n = O.
Proof.
    intro. destruct n.
    - intros. destruct H. reflexivity.
    - intros. simpl. reflexivity.
Qed.

Lemma succ_diff_zero: forall n : nat,
    S n <> O.
Proof.
    intros. discriminate.
Qed.

Lemma succ_eq_plus_one: forall n : nat,
    (S n) = n + (S O).
Proof.
    intros. induction n as [|k].
    - simpl. reflexivity.
    - simpl. rewrite IHk. reflexivity.
Qed.

Lemma mult_k_mais_um_left: forall n m : nat, 
    ((S O) + m) * n = n + (m*n).
Proof.
    intros. induction n as [|k].
    - simpl. rewrite mult_per_zero_right. simpl. reflexivity.
    - simpl ((S O + m) * (S k)). rewrite comutativity_sum.
        rewrite comutativity_mult. reflexivity.
Qed.

Lemma n_plus_one_eq_one: forall n : nat,
    (S O) = (S O) + n -> O = n.
Proof.
    intros. induction n as [|k].
    - reflexivity.
    - contradict H. discriminate.
Qed.

Lemma add_one_both_sides: forall n m : nat,
    n = m -> (S O) + n = (S O) + m.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Lemma sub_one_both_sides: forall n m : nat,
    S n = S m -> (S n) - (S O) = (S m) - (S O).
Proof.
    intros. rewrite H. reflexivity.
Qed.

Lemma succ_all_eq_succ_one: forall n m : nat,
    S(n + m) = (S n) + m.
Proof.
    intros. simpl. reflexivity. 
Qed.

Lemma minus_zero: forall m : nat,
    m - O = m.
Proof.
    intros. induction m as [|k].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma succ_minus_one: forall m : nat,
    (S m) - (S O) =  m.
Proof.
    intros. simpl. apply minus_zero.
Qed.

Lemma succ_minus_eq: forall m b c : nat, 
    (m = b - c) -> S m = S (b - c).
Proof.
    intros. simpl. apply add_one_both_sides in H.
    simpl in H. apply H.
Qed.

Lemma less_one_both_sides: forall n m : nat,
    ((S O) + n) = ((S O) + m) -> n = m.
Proof.
    intros. apply sub_one_both_sides in H. simpl in H.
    replace (n - O) with (n) in H. 
    replace (m - O) with (m) in H.
    - apply H.
    - destruct m.
        + simpl. reflexivity.
        + simpl. reflexivity.
    - destruct n.
        + simpl. reflexivity.
        + simpl. reflexivity.
Qed.

Lemma elim_brackets_right: forall a b c : nat, 
    a + b + c = a + (b + c).
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - simpl. replace (k+b+c) with (k+(b+c)). reflexivity.
Qed.

Lemma sub_same_both_sides: forall a b c : nat, 
    a = b -> a - c = b - c.
Proof.
    intros. rewrite H. reflexivity. 
Qed.

Lemma comutativity_sum3: forall a b c : nat,
    a + (b + c) = b + (a + c).
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - simpl. symmetry. rewrite comutativity_sum.
        rewrite <- succ_all_eq_succ_one.
        symmetry.
        rewrite elim_brackets_right.
        rewrite (comutativity_sum c).
        reflexivity.
Qed.

Lemma distributivity_mult_left: forall a b c : nat,
    a * (b + c) = a * b + a * c.
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - replace (S k * (b + c)) with ((S O + k) * (b + c)).
        + rewrite mult_k_mais_um_left. 
            rewrite comutativity_sum.
            symmetry.
            rewrite succ_eq_plus_one.
            rewrite(comutativity_sum (k)).
            rewrite mult_k_mais_um_left.
            rewrite IHk.
            rewrite mult_k_mais_um_left.
            rewrite (comutativity_sum b).
            simpl.
            rewrite (comutativity_sum ((k*b) + b)).
            symmetry.
            rewrite (comutativity_sum (k*b)).
            rewrite (comutativity_sum b).
            rewrite (comutativity_sum3).
            symmetry.
            rewrite elim_brackets_right.
            rewrite (elim_brackets_right (k*c)).
            reflexivity.
        + simpl. reflexivity.
Qed.

Lemma div_both_sides: forall a b c: nat,
    (a = b) -> (a/c = b/c).
Proof.
    intros. rewrite H. reflexivity.
Qed.

Lemma zero_div: forall a : nat,
    O / a = O.
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - simpl. reflexivity. 
Qed.

Lemma div_itself: forall n : nat, 
    (n <> O) -> (n/n = (S O)).
Proof.
    intro. apply contra_pos.
Qed.

Lemma div_same_result: forall a b : nat,
    (S a)/(S a) = (S b)/(S b).
Proof.
    intros. induction a as [|k].
    - destruct b.
Qed.


(* contradict serve para mostrar que uma hipótese é falsa, e
    logo se ela é falsa se tem qualquer coisa *)

Lemma div_eq_div_succs: forall a : nat,
    (S a)/(S a) = S O -> (S (S a))/(S (S a)) = S O.
Proof.
    intros. induction a as [|k].
    - simpl. reflexivity.
    - rewrite <- H.
Qed.


Lemma div_eq_one: forall n: nat,
    (S n)/(S n) = (S O).
Proof.
    intros. induction n as [|k].
    - simpl. reflexivity.
    - rewrite <- IHk.
        
Qed.

Lemma mult_div_without_change: forall a k : nat,
    k*(a/k) = a.
Proof.
    intros. induction a as [|H].
    - rewrite div_zero. rewrite mult_per_zero_right. reflexivity.
    - destruct H. 
Qed.


Theorem classic_even: forall a : nat,
    (even a = true) <-> (exists m : nat, a = (S (S O))*m).
Proof.
    intros. split.
    - intro. simpl. exists m.
Qed.

End tutorial.