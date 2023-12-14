Require Export Arith.
Require Export PeanoNat.
From Coq Require Import Unicode.Utf8_core.

Definition multiple (a b : nat) :=
    ∃ q : nat, (a = b * q).

Definition Even (n : nat) :=
    ∃ m : nat, (n = 2 * m).

Theorem even_multiple_two: ∀ n : nat, 
    Even n -> multiple n 2.
Proof.
    intros. unfold Even in *. unfold multiple. destruct H.
    exists x. apply H.
Qed.

Definition Odd (n : nat) :=
    ∃ m : nat, (n = 2 * m + 1).

Theorem odd_or_even:
    ∀ n : nat, Even n \/ Odd n.
Proof.
    intros. induction n.
    - left. unfold Even. exists 0. reflexivity.
    - destruct IHn.
        -- right. unfold Even in *. unfold Odd in *.
        destruct H. exists x. rewrite <- H. Search (_ + 1 = S _).
        rewrite Nat.add_1_r. reflexivity.
        -- left. unfold Even. unfold Odd in H. destruct H. exists (x + 1).
        rewrite H. simpl. rewrite Nat.add_1_r. rewrite Nat.add_0_r.
        rewrite Nat.add_0_r. rewrite Nat.add_assoc. rewrite Nat.add_1_r.
        rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
    match n with
    | 0 => true
    | 1 => false
    | S (S n) => even n
    end.

Lemma Odd_eq_not_Even:
    ∀ n : nat, (Odd n <-> ~ Even n).
Proof.
    intros. split.
    - intro. induction n as [|k].
        -- destruct H. rewrite Nat.add_1_r in H. discriminate H.
        -- intro. apply IHk.
            --- destruct H0. unfold Odd. destruct x.
                + simpl in H0. discriminate H0.
                + simpl in H0. injection H0. intros. rewrite Nat.add_0_r in H1.
                Search (_ + S _). rewrite Nat.add_succ_r in H1.
                exists x. simpl. rewrite Nat.add_0_r. rewrite Nat.add_1_r. apply H1.
            --- destruct H. unfold Even. exists x. rewrite Nat.add_1_r in H.
            injection H. intros. simpl. apply H1.
    - intros. unfold not in H. pose proof odd_or_even. specialize (H0 n).
    destruct H0.
        -- apply H in H0. destruct H0.
        -- apply H0.
Qed.

Lemma Even_eq_not_Odd:
    ∀ n : nat, Even n <-> ~ Odd n.
Proof.
    intros. split.
    - intros. intro. induction n as [|k IHk].
        -- destruct H0. rewrite Nat.add_1_r in H0. discriminate H0.
        --  apply IHk.
            + unfold Even. destruct H0. rewrite Nat.add_1_r in H0. injection H0.
            intros. exists x. simpl. apply H1.
            + destruct H. unfold Odd. destruct x.
                ++ simpl in H. discriminate H.
                ++ simpl in H. injection H. intros. rewrite Nat.add_succ_r in H1.
                rewrite Nat.add_0_r in H1. exists x. simpl. rewrite Nat.add_succ_r.
                rewrite Nat.add_0_r. rewrite Nat.add_0_r. apply H1.
    - intros. pose proof odd_or_even. 
Qed.

Theorem even_classic_def: 
    ∀ n : nat, (even n) = true <-> Even n.
Proof.
    intros. split.
    - intros. pose proof odd_or_even. specialize (H0 n). destruct H0.
        -- apply H0.
        -- destruct H0. unfold Even.
        
Qed.