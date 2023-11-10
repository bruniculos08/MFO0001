(* Aluno: Bruno Rafael dos Santos *)
Require Export Arith.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n as [|k].
  - apply le_n.
  - apply le_S. apply IHk.
Qed.

Print le_n.

Lemma less_one_le: forall n m,
  S n <= m -> n <= m.
Proof.
  intros. induction H.
  - apply le_S. apply le_n.
  - apply le_S in IHle. apply IHle.
Qed. 

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S in IHle. apply IHle.
Qed.

Lemma n_le_m__Sn_le_Sm' : forall a b, 
  a <= b -> S a <= S b.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S in IHle. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - apply le_n.
  - apply less_one_le. apply H1.
Qed.

Lemma le_trans : forall m n o, 
  m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0.
  - apply H.
  - apply le_S in IHle. apply IHle.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction b as [|k].
  - Search(plus). rewrite Nat.add_0_r. apply le_n.
  - rewrite Nat.add_succ_r. apply le_S. apply IHk.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros. unfold lt. generalize dependent m.
  induction n as [|k].
  - intros. destruct m.
    -- right. unfold ge. apply le_n.
    -- left. apply n_le_m__Sn_le_Sm. apply O_le_n.
  - intros. specialize (IHk m). destruct IHk.
    -- inversion H.
      --- right. unfold ge. apply le_n.
      --- unfold ge. rewrite <- H1 in H.
      left. apply n_le_m__Sn_le_Sm in H0. apply H0.
    -- right. unfold ge in *. apply le_S. apply H. 
Qed.

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).

Lemma n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros. apply le_S' in H. apply H.
Qed.

Lemma le'_n_n : forall a, le' a a.
Proof.
  intros. induction a as [|k].
  - apply le_0'.
  - apply le_S'. apply IHk.
Qed.  
  
Lemma le'_n_Sm : forall a b, 
  le' a b -> le' a (S b). 
Proof.
  intros. induction H.
  - apply le_0'.
  - apply le_S'. apply IHle'.
Qed.

Theorem le_le' : forall a b, 
  le a b <-> le' a b.
Proof.
  intros. split.
  - intros. induction H.
    -- apply le'_n_n.
    -- apply le'_n_Sm. apply IHle.
  - intros. induction H.
    -- apply O_le_n.
    -- apply n_le_m__Sn_le_Sm. apply IHle'.
Qed. 

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros. unfold lt in *. 
  pose proof le_trans. pose proof le_plus_l.
  split.
  - specialize (H1 n1 n2) as H2. apply n_le_m__Sn_le_Sm' in H2.
  specialize (H0 (S n1) (S (n1 + n2)) m). apply H0 in H.
    -- apply H.
    -- apply H2.
  - specialize (H1 n2 n1) as H2. rewrite Nat.add_comm in H2.
  apply n_le_m__Sn_le_Sm in H2. specialize (H0 (S n2) (S (n1 + n2)) m).
  apply H0 in H2.
    -- apply H2.
    -- apply H.
Qed.

Theorem lt_S : forall n m,
  n < m -> n < S m.
Proof.
  intros. unfold lt in *. apply le_S in H. apply H.
Qed.