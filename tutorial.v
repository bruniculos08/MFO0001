Module tutorial.
Inductive bool :=
    |True
    |False.
Check True.

Definition andb(a b: bool): bool := 
    match a with 
    |False => False
    |True => b
    end.

Compute andb True True.

Definition orb(a b: bool): bool :=
    match a with
    |True => True
    |False => b
    end.

Compute orb True False.

Definition notb(a : bool): bool :=
    match a with
    |True => False
    |False => True
    end.

Definition implieb(a b : bool): bool :=
    match a with
    | False => True
    | True => b
    end.

Example and_example: andb True False = False.
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
    | O => True
    | S O => False
    | S(S n) => even n
    end.

Fixpoint sum(a b : nat) : nat :=
    match a with
    | O => b
    | S(n) => S(sum n b)
    end.

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
    | O, b => O
    | a, O => a
    | S(n), S(m) => sub n m
    end.

Compute sub (S O) (S (S (S O))).

Fixpoint div(a b : nat) : nat :=
    match a, b with

End tutorial.