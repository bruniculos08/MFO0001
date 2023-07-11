Module tutorial.
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
            | S n, O => O
            | O, S m => O
            | S n, S m => S (div (sub n m) (S m))
            end
    end.

Compute div (S(S O)) (S(S O)).

Lemma aux_com_sum:forall a b: nat,
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


Theorem classic_even: forall a : nat,
    (even a = true) <-> (exists m : nat, a = (S (S O))*m).
Proof.
    intros. induction a as [|k].
    - split.
        + simpl. exists O. simpl. reflexivity.
        + intros. simpl. reflexivity.
    - split.
        + destruct IHk.
Qed.

End tutorial.