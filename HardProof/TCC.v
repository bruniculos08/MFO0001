From Coq Require Import Unicode.Utf8_core.

(* Manter organizado *)


(* Este módulo contém uma implementação própria
de números inteiros *)
Module MyInteger.

Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Inductive Integer : Type :=
    | Positive (n : nat) : Integer
    | Negative (n : nat) : Integer
    .

Fixpoint int_add (a b : Integer) :=
    match a, b with
    | Positive 0, X => X 
    | Negative 0, X => X 
    | X, Positive 0 => X 
    | X, Negative 0 => X 
    | Positive m, Positive n => Positive (m + n)
    | Negative m, Negative n => Negative (m + n)
    | Positive m, Negative n => if m <=? n then Negative (n - m)
                                else Positive (m - n)
    | Negative m, Positive n => if n <=? m then Negative (n - m)
                                else Positive (m - n)
    end.

End MyInteger.

(* Este módulo contém a implementação parcial de
inteiros como pares de naturais descrita em:
https://perso.crans.org/cohen/papers/quotients.pdf *)
Module PairInteger.

Definition int_axiom (z : nat * nat) :=
    (fst z = 0) \/ (snd z = 0). 

Definition int := {z | int_axiom z}.

(* Definition reprZ (n : int) : nat * nat := val n. *)

End PairInteger.

(* Este módulo contém a implementação de inteiros
da biblioteca ZArith descrita em:
https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.ZArith.Int.html

OBS.: essa biblioteca também contém código relacionado
a teoria dos números (ZArith.Znumtheory), descrito em:
https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.ZArith.Znumtheory.html*)
Module IntegerZArith.
    
Require Export ZArith.
Require Export Coq.ZArith.Int.

End IntegerZArith.

(* Este módulo serve para código de exercícios e "testes" 
relacionados a teoria dos números (para o TCC)*)
Module ToyPlayground.

Require Export Arith.
Require Export Bool.
Require Export PeanoNat.
Require Export Init.Wf.

Search (Nat.divmod).

Lemma divmod_spec:
    ∀ x y q u : nat,
    u <= y
    → let (q', u') := Nat.divmod x y q u in
    x + S y * q + (y - u) = S y * q' + (y - u') ∧ u' <= y .
Proof.
    intros. destruct (Nat.divmod x y q u) eqn:Case1.
    split.
    - generalize dependent y.
    generalize dependent q. generalize dependent u.
    induction x.
        -- intros. simpl in Case1. injection Case1. intros.
        subst n0. subst n. reflexivity.
        -- intros. simpl in Case1. destruct u.
            + specialize (IHx y (S q) y).
            assert (y <= y). { apply le_n. }
            apply IHx in H0. rewrite Nat.sub_diag in H0.
            rewrite Nat.add_0_r in H0.
            rewrite Nat.mul_succ_r in H0.
            rewrite Nat.sub_0_r.
            repeat rewrite Nat.add_succ_l.
            rewrite <- Nat.add_succ_r.
            rewrite Nat.add_assoc in H0.
            assumption.
            assumption.
            + specialize (IHx u q y).
            rewrite Nat.add_sub_assoc.
                ++ rewrite Nat.add_succ_l.
                rewrite Nat.add_succ_l.
                rewrite <- Nat.add_succ_r.
                rewrite <- Nat.add_sub_assoc.
                simpl (S y - S u).
                apply IHx.
                    * transitivity (S u).
                    apply le_S. apply le_n.
                    assumption.
                    * assumption.
                    * transitivity y.
                    assumption.
                    apply le_S. apply le_n.
                ++ assumption.
    - generalize dependent u.
    generalize dependent y.
    generalize dependent q. 
    induction x.
        -- intros. simpl in Case1. injection Case1.
        intros. subst n0. assumption.
        -- intros.
        simpl in Case1. destruct u.
            + specialize (IHx (S q) y y).
            apply IHx.
            apply le_n.
            assumption.
            + specialize (IHx q y u).
            apply IHx. 
            transitivity (S u).
            apply le_S. apply le_n.
            assumption.
            assumption. 
Qed.

Lemma zero_mod_n:
    ∀ n, 0 mod n = 0.
Proof.
    intros. induction n.
    - simpl. reflexivity.
    - simpl. rewrite Nat.sub_diag. reflexivity.
Qed. 

Lemma div_zero_n:
    ∀ n, 0/n = 0.
Proof.
    intros. induction n.
    - reflexivity.
    - simpl. reflexivity.
Qed.

Lemma divmod_correctness:
    ∀ a b, b <> 0 -> a = b * (a / b) + (a mod b) /\ (a mod b) < b.
Proof.
    intros. generalize dependent b.
    induction a.
    + intros. rewrite zero_mod_n. rewrite Nat.add_0_r.
    rewrite div_zero_n. rewrite Nat.mul_0_r. split.
        ++ reflexivity.
        ++ destruct b.
            - destruct H. reflexivity.
            - apply Nat.lt_0_succ.
    + intros. apply IHa in H as H0.
    destruct H0.
    destruct b.
        ++ destruct H. reflexivity.
        ++ pose proof Nat.divmod_spec.
        simpl in H0. simpl in H1.
        destruct (Nat.divmod a b 0 b) eqn:Case1.
        simpl in H0. simpl in H1. simpl. destruct b.
                * specialize (H2 a 0 1 0).
                assert (0 <= 0). { apply le_n. }
                apply H2 in H3. destruct (Nat.divmod a 0 1 0).
                simpl in H3. destruct H3. 
                repeat rewrite Nat.add_0_r in H3.
                simpl. repeat rewrite Nat.add_0_r.
                rewrite Nat.add_1_r in H3. split.
                    ** apply H3.
                    ** unfold lt. apply le_n.
                * specialize (H2 a (S b) 0 b).
                assert (b <= S b). { apply le_S. apply le_n. }
                apply H2 in H3. destruct (Nat.divmod a (S b) 0 b) eqn:Case2.
                destruct H3. simpl (fst (n1, n2) + S b * fst (n1, n2)).
                simpl (snd (n1, n2)). rewrite Nat.mul_0_r in H3.
                rewrite Nat.add_0_r in H3. 
                assert (S b - b = 1). 
                {
                    rewrite Nat.sub_succ_l.
                    - rewrite Nat.sub_diag. reflexivity.
                    - apply le_n.
                }
                rewrite H5 in H3. rewrite Nat.add_1_r in H3. 
                simpl ( S (S b) * n1) in H3. split.
                    ** apply H3.
                    ** unfold lt. Search (S _ <= S _).
                    rewrite <- Nat.succ_le_mono.
                    apply Nat.le_sub_l.
Qed.

Definition divides (a b : nat) :=
    ∃ q, b = a * q.

Notation "a ∣ b" := (divides a b) (at level 0, right associativity).

Definition gcd (a b n : nat) :=
    (n ∣ a) /\ (n ∣ b) /\ ∀ x, (x ∣ a) /\ (x ∣ b) -> (x ∣ n).

Lemma gcd_zero_r: 
    ∀ n, Nat.gcd n 0 = n.
Proof.
    intros. induction n.
    - simpl. reflexivity.
    - simpl. rewrite Nat.sub_diag. simpl. reflexivity. 
Qed.

(* Prova de que o algoritmo de Euclides funciona *)
Theorem Euclides: 
    ∀ a b, a <> 0 -> Nat.gcd a b = Nat.gcd (b mod a) a.
Proof.
    intros. generalize dependent a. induction b.
    - intros. rewrite zero_mod_n. simpl. rewrite gcd_zero_r.
    reflexivity.
    - intros. symmetry. destruct a.
        -- destruct H. reflexivity.
        -- simpl. destruct a.
            + reflexivity.
            + reflexivity.   
Qed.

Lemma divisible_diff:
    ∀ a b : nat, ∀ n : nat, (n ∣ a) /\ (n ∣ b) -> (n ∣ (a - b)).
Proof.
    intros. unfold divides in *. destruct H. destruct H.
    destruct H0. exists (x - x0). Search (_ * (_ - _)).
    rewrite Nat.mul_sub_distr_l. rewrite H. rewrite H0.
    reflexivity.
Qed.

Lemma div2_both_sides: 
    ∀ m n, m = n -> Nat.div2 m = Nat.div2 n. 
Proof.
    intros. rewrite H. reflexivity. 
Qed.

Lemma divmod_eq1:
    ∀ n, fst (Nat.divmod (n * (n - 1)) 1 0 1) + n = fst(Nat.divmod (n - 0 + n * (n - 0)) 1 0 1).
Proof.
    intros.
    pose proof (Nat.divmod_spec (n * (n - 1)) 1 0 1).
    assert (1 <= 1). { apply le_n. }
    apply H in H0 as H1.
    destruct (Nat.divmod (n * (n - 1)) 1 0 1) eqn:Case1.
    rewrite Nat.mul_0_r in H1. rewrite Nat.add_0_r in H1.
    rewrite Nat.add_0_r in H1. destruct H1.
    pose proof (Nat.divmod_spec (n - 0 + n * (n - 0)) 1 0 1 H0).
    destruct (Nat.divmod (n - 0 + n * (n - 0)) 1 0 1) eqn:Case2.
    rewrite Nat.sub_0_r in H3.
    rewrite Nat.mul_0_r in H3. rewrite Nat.sub_diag in H3.
    repeat rewrite Nat.add_0_r in H3. destruct H3.
    simpl. inversion H2.
        - inversion H4.
            -- subst n3. subst n1. simpl in H1.
            repeat rewrite Nat.add_0_r in H1.
            simpl in H3.
            repeat rewrite Nat.add_0_r in H3.
            destruct n.
                + simpl in H1.
                symmetry in H1.
                apply Nat.eq_add_0 in H1.
                destruct H1. subst n0.
                simpl in H3.
                symmetry in H3.
                apply Nat.eq_add_0 in H3.
                destruct H3. subst n2.
                reflexivity.
                + simpl in H1.
                rewrite Nat.sub_0_r in H1.
                simpl in H3.
                rewrite Nat.mul_succ_r in H3.
                rewrite Nat.add_succ_r in H3.
                rewrite (Nat.add_comm (n*n) )in H3.
                rewrite H1 in H3.
                Search (Nat.div2).
                Search (Nat.double).
                assert (n2 + n2 = 2 * n2).
                {
                 simpl. rewrite Nat.add_0_r. reflexivity.   
                }
                assert (S (S (n + (n + (n0 + n0)))) = 2 * (S n) + 2 * n0).
                {
                 simpl. rewrite Nat.add_0_r.
                 rewrite Nat.add_succ_r.
                 simpl. rewrite Nat.add_0_r.
                 rewrite Nat.add_assoc.
                 reflexivity.   
                }
                rewrite H5 in H3.
                rewrite H6 in H3.
                assert (2 * S n + 2 * n0 = 2 * ((S n) + n0)).
                {
                 simpl. repeat rewrite Nat.add_0_r.
                 rewrite Nat.add_assoc.
                 symmetry.
                 rewrite Nat.add_succ_r.
                 simpl.
                 rewrite Nat.add_assoc.
                 rewrite (Nat.add_comm n).  
                 rewrite <- Nat.add_assoc.
                 rewrite (Nat.add_comm n n0).
                 rewrite Nat.add_assoc.
                 rewrite <- Nat.add_assoc.
                 rewrite <- Nat.add_assoc.
                 rewrite (Nat.add_comm n).
                 rewrite Nat.add_assoc.
                 apply f_equal.
                 rewrite Nat.add_succ_r.
                 simpl.
                 apply f_equal.
                 rewrite <- Nat.add_assoc.
                 rewrite <- Nat.add_assoc.
                 rewrite Nat.add_comm.
                 rewrite (Nat.add_comm n0).
                 reflexivity.
                }
                rewrite H7 in H3.
                apply div2_both_sides in H3.
                rewrite Nat.div2_double in H3.
                rewrite Nat.div2_double in H3.
                rewrite Nat.add_comm in H3. apply H3.
            -- subst m. subst n1.
            rewrite Nat.sub_diag in H1.
            rewrite Nat.add_0_r in H1. destruct n.
                + simpl in H1. rewrite Nat.add_0_r in H1.
                symmetry in H1. rewrite Nat.eq_add_0 in H1.
                destruct H1. subst n0.
                simpl (2 * n2) in H3.
                symmetry in H3.
                rewrite <- Nat.add_assoc in H3.
                apply Nat.eq_add_0 in H3.
                destruct H3.
                subst n2. reflexivity.
                + inversion H7. subst n3.
                simpl (1 - 0) in H3.
                rewrite Nat.add_1_r in H3.
                rewrite Nat.add_comm in H3.
                rewrite Nat.add_succ_r in H3.
                injection H3 as H3.
                rewrite Nat.mul_succ_r in H3.
                simpl (S n - 1) in H1.
                rewrite Nat.sub_0_r in H1.
                simpl (S n * n) in H1.
                rewrite Nat.add_comm in H1.
                rewrite H1 in H3.
                rewrite Nat.add_0_r in H3.
                simpl in H3.
                rewrite Nat.add_0_r in H3.
                assert (S (n + (n0 + n0) + n) = 2 * (n + n0) + 1).
                {
                 simpl. rewrite Nat.add_1_r.
                 rewrite Nat.add_0_r.
                 symmetry.
                 rewrite <- Nat.add_assoc.
                 rewrite (Nat.add_comm n n0).
                 rewrite Nat.add_assoc.   
                 rewrite Nat.add_assoc.
                 rewrite Nat.add_assoc.
                 reflexivity.
                }
                rewrite H5 in H3.
                assert (n2 + n2 = 2 * n2).
                {
                 simpl. rewrite Nat.add_0_r. reflexivity.   
                }
                rewrite H6 in H3.
                Search (Nat.Even).
                exfalso.
                apply (Nat.Even_Odd_False (2 * n2)).
                    ++ unfold Nat.Even. exists n2. 
                    reflexivity.
                    ++ rewrite <- H3. exists (n + n0).
                    reflexivity.
    - subst m. inversion H4.
        -- subst n3. inversion H6. subst n1.
        rewrite Nat.sub_0_r in H1.
        rewrite Nat.sub_diag in H3.
        rewrite Nat.add_0_r in H3.
        destruct n.
            + simpl in H1. symmetry in H1.
            rewrite <- Nat.add_assoc in H1.
            rewrite Nat.eq_add_0 in H1.
            destruct H1. subst n0. simpl in H5.
            discriminate H5.
            + simpl (S n * (S n - 1)) in H1.
            rewrite Nat.sub_0_r in H1.
            simpl (S n + S n * S n) in H3.
            rewrite Nat.add_succ_r in H3.
            rewrite Nat.mul_succ_r in H3.
            rewrite (Nat.add_comm (n * n)) in H3.
            rewrite H1 in H3.
            rewrite Nat.add_1_r in H3.
            rewrite Nat.add_succ_r in H3.
            assert (S (S (n + S (n + 2 * n0))) = 2 * (n + n0 + 1) + 1).
            {
             simpl. repeat rewrite Nat.add_1_r.
             repeat rewrite Nat.add_0_r.
             rewrite Nat.add_succ_r.   
             rewrite Nat.add_succ_r.
             rewrite Nat.add_succ_l.
             repeat apply f_equal.
             rewrite <- Nat.add_assoc.
             symmetry.
             rewrite (Nat.add_comm n0).
             rewrite <- Nat.add_assoc.
             reflexivity.
            }
            rewrite H5 in H3.
            exfalso.
            apply (Nat.Even_Odd_False (2 * n2)).
                ++ exists n2. reflexivity.
                ++ rewrite <- H3. exists (n + n0 + 1).
                reflexivity.
        -- subst m. inversion H7. subst n3.
        inversion H6. subst n1. destruct n.
            + simpl in H1. rewrite Nat.add_1_r in H1.
            discriminate H1.
            + simpl (1 - 0 ) in H1.
            simpl (S n - 1) in H1.
            rewrite Nat.sub_0_r in H1.
            simpl (1 - 0) in H3.
            simpl (S n + S n * S n) in H3.
            rewrite Nat.mul_comm in H3.
            rewrite H1 in H3.
            rewrite Nat.add_1_r in H3.
            rewrite Nat.add_1_r in H3.
            rewrite Nat.add_succ_r in H3.
            injection H3 as H3.
            rewrite Nat.add_0_r in H3.
            rewrite Nat.add_0_r in H3.
            assert (S (n + (n + S (n0 + n0))) = 2 * (n + n0 + 1)).
            {
             simpl. rewrite Nat.add_1_r.
             rewrite Nat.add_0_r. rewrite Nat.add_succ_r.   
             rewrite Nat.add_succ_r.    
             rewrite Nat.add_succ_r.
             rewrite Nat.add_succ_l.
             apply f_equal.    
             apply f_equal.
             symmetry.
             rewrite <- Nat.add_assoc.
             rewrite (Nat.add_comm n0).
             rewrite <- Nat.add_assoc.
             reflexivity.    
            }
            rewrite H5 in H3.
            assert (n2 + n2 = 2 * n2).
            {
             simpl. rewrite Nat.add_0_r. reflexivity.   
            }
            apply div2_both_sides in H3.
            rewrite H8 in H3.
            rewrite Nat.div2_double in H3.
            rewrite Nat.div2_double in H3.
            rewrite Nat.add_1_r in H3. 
            rewrite Nat.add_comm in H3.
            rewrite Nat.add_succ_r. apply H3.
Qed.

Lemma gcd_end:
    ∀ a b, ∃ n, (Nat.gcd a b = Nat.gcd 0 n).
Proof.
    fix gcd_end 1.
    intros. destruct a.
    - simpl. exists b. reflexivity.
    - rewrite Euclides.
        -- apply (gcd_end (b mod S a) (S a)).
        -- intro. discriminate H.
Qed.

Theorem strong_induction (P : nat -> Prop):
    (∀ m, (∀ k,  k < m -> P k) -> P m) -> ∀ n, P n.
Proof.
    intros. apply H. intros. generalize dependent k.
    induction n.
    - intros. inversion H0.
    - intros. apply H. intros. 
    assert (k0 < n). 
    {
        unfold lt in *. Search (_ <= _). 
        apply le_S_n in H0.
        transitivity k.
        - apply H1.
        - apply H0.
    }
    apply IHn. apply H2.
Qed.

Lemma mod_less:
    ∀ n m, m <> 0 /\ n < m -> m mod (S n) < m.
Proof.
    induction m.
    - intros. destruct H. inversion H0.
    - intros. destruct H. destruct m.
        -- inversion H0.
            + subst n. simpl. unfold lt. apply le_n.
            + inversion H2.
        -- unfold Nat.modulo. destruct (snd (Nat.divmod (S (S m)) n 0 n)).
            + rewrite Nat.sub_0_r. apply H0.
            + Search (_ - _ < _). unfold lt in *.
            rewrite <- Nat.succ_le_mono. 
            rewrite <- Nat.succ_le_mono in H0. 
            rewrite Nat.le_sub_le_add_l.
            rewrite Nat.add_comm.
            transitivity (S m).
                ++ apply H0.
                ++ Search (_ <= _ + _).
                apply Nat.le_add_r.
Qed.

Lemma eq_add_0:
    ∀ m n, m = m + n -> n = 0.
Proof.
    intros. induction m.
    - simpl in H. rewrite H. reflexivity.
    - apply IHm. simpl in H. injection H as H. apply H.
Qed.

Lemma eq_sub_0:
    ∀ m n, m <> 0 /\ m = m - n -> n = 0.
Proof.
    intros. generalize dependent n. induction m.
    - intros. destruct H. destruct H. reflexivity.
    - intros. destruct H. destruct n.
        -- reflexivity.
        -- Search (_ <= _ \/ _ < _).
        pose proof (Nat.le_gt_cases m (S n)).
        destruct H1.
            + inversion H1.
                ++ rewrite <- H2 in H0.
                rewrite Nat.sub_succ_l in H0.
                    * injection H0 as H0.
                    rewrite Nat.sub_diag in H0.
                    subst m. discriminate H2.
                    * apply le_n.
                ++ apply Nat.succ_le_mono in H3.
                Search (_ - _ = 0).
                apply Nat.sub_0_le in H3.
                rewrite H3 in H0.
                discriminate H0.
            + unfold lt in H1. Search (_ <= _).
            rewrite Nat.sub_succ_l in H0.
                ++ injection H0 as H0.
                destruct m.
                    * inversion H1.
                    * destruct (IHm (S n)).
                        ** split.
                            *** intro. discriminate H2.
                            *** apply H0.
                        ** reflexivity.
                ++ transitivity (S (S n)).
                    * apply le_S. apply le_n.
                    * apply H1.              
Qed.

Lemma random_equation_0:
    ∀ n n0 n1, n <> 0 /\ n = n0 * S n + (n - n1) -> n0 = 0 /\ n1 = 0.
Proof.
    intros. destruct n0.
    - split.
        -- reflexivity.
        -- apply eq_sub_0 with (m := n).
        simpl in H. apply H.
    - destruct H. simpl in H0.
    rewrite <- Nat.add_succ_r in H0.
    rewrite <- Nat.add_assoc in H0.
    apply eq_add_0 in H0.
    rewrite Nat.add_succ_r in H0.
    discriminate H0.
Qed.        

Lemma random_equation_1:
    ∀ n m x, m <= n /\ m = n + S x -> False. 
Proof.
    intros. destruct H.
    rewrite H0 in H.
    Search (_ <= _).
    apply le_not_lt in H as H1.
    apply H1. unfold lt.
    rewrite Nat.add_succ_r.
    rewrite <- Nat.succ_le_mono.
    apply Nat.le_add_r.
Qed.
        
Lemma mod_biger:
    ∀ m n, m < n -> m mod n = m.
Proof.
    intros. generalize dependent m.
    induction n.
    - intros. inversion H.
    - intros. inversion H.
        -- simpl. pose proof (Nat.divmod_spec n n 0 n).
        destruct (Nat.divmod n n 0 n) eqn:Case1.
        destruct H0.
            + apply le_n.
            + simpl. simpl in H0.
            rewrite Nat.mul_0_r in H0.
            rewrite Nat.sub_diag in H0.
            rewrite Nat.add_0_r in H0. 
            rewrite Nat.add_0_r in H0.
            rewrite (Nat.add_comm n0) in H0.
            rewrite Nat.mul_comm in H0.
            rewrite <- Nat.mul_succ_r in H0.
            pose proof random_equation_0.
            destruct n0.
                ++ simpl in H0. symmetry.
                apply H0.
                ++ simpl in H0.
                rewrite <- Nat.add_succ_r in H0.
                rewrite <- Nat.add_assoc in H0.
                apply eq_add_0 in H0.
                rewrite Nat.add_succ_r in H0.
                discriminate H0.
        -- subst m0. simpl.
        pose proof (Nat.divmod_spec m n 0 n).
        destruct (Nat.divmod m n 0 n).
        simpl. destruct H0.
            + apply le_n.
            + rewrite Nat.mul_0_r in H0.
            rewrite Nat.add_0_r in H0.
            rewrite Nat.sub_diag in H0.
            rewrite Nat.add_0_r in H0.
            unfold lt in H.  
            destruct n0.
                ++ simpl in H0.
                rewrite Nat.mul_0_r in H0.
                simpl in H0.
                symmetry.
                apply H0.
                ++ rewrite Nat.mul_succ_r in H0.
                pose proof random_equation_1.
                rewrite <- Nat.succ_le_mono in H.
                simpl in H0.
                rewrite (Nat.add_comm _ (S n)) in H0.
                rewrite <- Nat.add_assoc in H0.
                rewrite Nat.add_succ_l in H0.
                rewrite <- Nat.add_succ_r in H0.
                exfalso.
                apply (H3 n m (n0 + n * n0 + (n - n1))).
                split.
                    * apply H.
                    * apply H0.
Qed.

Lemma random_equation_2:
    ∀ m n, ~ ( S (S m) = S m - n).
Proof.
    intros. intro. generalize dependent m.
    induction m.
    - intros. simpl in H. destruct n.
        -- discriminate H.
        -- discriminate H.
    - intros. apply IHm. 
    pose proof (Nat.le_gt_cases n (S m)).
    destruct H0.
        -- rewrite Nat.sub_succ_l in H.
            + injection H as H.
            simpl. apply H.
            + apply H0.
        -- Search (_ - _ = 0).
        apply Nat.sub_0_le in H0 as H1.
        rewrite H1 in H. discriminate H.
Qed.

Lemma mod_equal:
    ∀ n, n mod n = 0.
Proof.
    apply strong_induction.
    intros. destruct m.
    - simpl. reflexivity.
    - simpl. destruct m.
        -- simpl. reflexivity.
        -- destruct (Nat.divmod (S m) (S m) 0 m) eqn:Case1.
        simpl (snd (n, n0)).
        pose proof (Nat.divmod_spec (S m) (S m) 0 m).
        rewrite Case1 in H0.
        destruct H0.
            + apply le_S. apply le_n.
            + rewrite Nat.mul_0_r in H0.
            rewrite Nat.add_0_r in H0.
            rewrite Nat.sub_succ_l in H0.
                ++ rewrite Nat.sub_diag in H0.
                rewrite Nat.add_1_r in H0.
                pose random_equation_0.
                destruct n.
                    * rewrite Nat.mul_0_r in H0.
                    rewrite Nat.add_0_l in H0.
                    apply random_equation_2 in H0.
                    destruct H0.
                    * destruct n.
                        ** rewrite Nat.mul_1_r in H0.
                        apply eq_add_0 in H0.
                        apply  H0.
                        ** rewrite Nat.mul_succ_r in H0.
                        rewrite (Nat.add_comm _ (S (S m))) in H0.
                        rewrite <- Nat.add_assoc in H0.
                        apply eq_add_0 in H0.
                        simpl in H0. discriminate H0.
                ++ apply le_n.
Qed.

Lemma gcd_comm:
    ∀ a b, Nat.gcd a b = Nat.gcd b a.
Proof.
    intros.
    pose proof (Nat.lt_trichotomy a b).
    destruct H.
    - symmetry.
    rewrite Euclides.
    apply mod_biger in H.
    rewrite H. reflexivity.
    intro. subst b. inversion H.
    - destruct H.
        -- rewrite H. reflexivity.
        -- rewrite Euclides.
        apply mod_biger in H.
        rewrite H. reflexivity.
        intro. subst a.
        inversion H.
Qed.

Lemma mod_less_r:
    ∀ m n, n <> 0 -> m mod n < n.
Proof.
    intros. pose proof (divmod_correctness m n).
    destruct H0.
    - apply H.
    - apply H1.
Qed.

Lemma mod_transitivity:
    ∀ a b c m : nat,
    a mod m = b mod m /\ b mod m = c mod m
    -> a mod m = c mod m.
Proof.
    intros. destruct H. rewrite H. rewrite H0.
    reflexivity.
Qed.

Lemma mod_meaning:
    ∀ a b m, m <> 0 -> (a mod m = b mod m -> m ∣ (a - b)).
Proof.
    intros. unfold divides.
    pose proof (divmod_correctness a m).
    pose proof (divmod_correctness b m).
    apply H1 in H as Ha.
    apply H2 in H as Hb. 
    destruct Ha.
    destruct Hb.
    rewrite H5.
    rewrite H3.
    Search (_ - _).
    rewrite Nat.add_comm.
    rewrite (Nat.add_comm (m * (b / m))).
    rewrite H0.
    rewrite <- minus_plus_simpl_l_reverse.
    exists ((a/m) - (b/m)).
    rewrite Nat.mul_sub_distr_l.
    reflexivity.
Qed.     

Lemma bigger_eq:
    ∀ m n, n < m -> ∃ x, m = n + x.
Proof.
    intros. generalize dependent m. induction n.
    - intros. exists m. reflexivity.
    - intros. destruct m.
        -- inversion H.
        -- specialize (IHn m).
        destruct IHn. unfold lt in *. apply Nat.succ_le_mono.
        assumption.
        exists x. rewrite Nat.add_succ_l.
        apply f_equal.
        apply H0.
Qed.

Lemma mod_meaning_full:
∀ a b m, m <> 0 -> (a mod m = b mod m <-> m ∣ (a - b) /\ m ∣ (b - a)).
Proof.
    intros. split.
    - intros. destruct m.
        -- exfalso. apply H. reflexivity.
        -- split.
            + apply mod_meaning.
                ++ assumption.
                ++ assumption.
            + symmetry in H0.
            apply mod_meaning.
                ++ assumption.
                ++ assumption.
    - intros. destruct H0. 
    destruct H0. destruct H1.
    pose proof (Nat.lt_trichotomy a b).
    destruct H2.
        -- pose proof (Nat.lt_trichotomy a m).
        destruct H3.
        pose proof (divmod_correctness b m).
        destruct H4.
            + apply H.
            + apply Nat.add_sub_eq_nz in H1.
            symmetry in H1.
            rewrite Nat.add_comm in H1.
            pose proof (Nat.div_mod_unique m x0 (b/m) a (b mod m)).
            destruct H6.
                ++ apply H3.
                ++ apply H5.
                ++ rewrite <- H1.
                rewrite <- H4. reflexivity.
                ++ symmetry. rewrite Nat.mod_eq.
                rewrite <- H6.
                rewrite H1.
                rewrite Nat.add_comm.
                rewrite Nat.add_sub.
                apply mod_biger in H3.
                rewrite H3. reflexivity.
                apply H.
                ++ intro. rewrite H6 in H1.
                Search (_ < _ -> _ - _ <> 0).
                apply Nat.sub_gt in H2.
                apply H2.
                apply H1.
            + destruct H3.
                ++ subst a. 
                rewrite mod_equal. symmetry.
                pose proof (divmod_correctness b m).
                destruct H3.
                apply H.
                rewrite Nat.mod_eq.
                    * apply Nat.add_sub_eq_nz in H1.
                    symmetry in H1.
                    rewrite Nat.add_comm in H1.
                    rewrite <- Nat.mul_succ_r in H1.
                    rewrite H1.
                    Search ((_ * _) / _).
                    rewrite Nat.mul_comm at 2.
                    rewrite Nat.div_mul.
                    rewrite Nat.sub_diag. reflexivity.
                    apply H.
                    intro. rewrite H5 in H1.
                    apply Nat.sub_gt in H2.
                    apply H2.
                    assumption.
                    * apply H.
                ++ apply Nat.add_sub_eq_nz in H1.
                symmetry in H1.
                pose proof (divmod_correctness b m).
                pose proof (divmod_correctness a m).
                destruct H4. apply H.
                destruct H5. apply H.
                rewrite H5 in H1.
                rewrite (Nat.add_comm (m * _)) in H1.
                Search (_ * (_ + _)).
                rewrite <- Nat.add_assoc in H1.
                rewrite <- Nat.mul_add_distr_l in H1.
                rewrite Nat.add_comm in H1.
                pose proof (Nat.div_mod_unique m (b/m) (a/m + x0) (b mod m) (a mod m)).
                destruct H8.
                assumption.
                assumption.
                rewrite <- H1.
                symmetry.
                assumption.
                rewrite H9. reflexivity.
                intro. rewrite H4 in H1.
                apply Nat.sub_gt in H2. apply H2.
                assumption.
        -- destruct H2.
        (* a = b *)
        rewrite H2. reflexivity.
        (* b < a *)
        apply Nat.add_sub_eq_nz in H0.
        symmetry in H0.
        pose proof (Nat.lt_trichotomy b m).
        destruct H3.
            + pose proof (divmod_correctness a m).
            destruct H4.
            apply H.
            rewrite Nat.add_comm in H0.
            pose proof (Nat.div_mod_unique m (a/m) x (a mod m) b).
            destruct H6.
            assumption.
            assumption.
            rewrite <- H4. assumption.
            rewrite H7. apply mod_biger in H3. rewrite H3. reflexivity.
            + destruct H3.
            (* b = m  *)
            subst b.
            rewrite Nat.mod_eq.
            rewrite Nat.add_comm in H0.
            rewrite <- Nat.mul_succ_r in H0.
            rewrite H0.
            rewrite Nat.mul_comm at 2.
            rewrite Nat.div_mul.
            rewrite Nat.sub_diag. rewrite mod_equal. reflexivity.
            apply H.
            apply H.
            (* m < b *)
            pose proof (divmod_correctness b m).
            destruct H4.
            apply H.
            rewrite H4 in H0.
            rewrite (Nat.add_comm _ (b mod m)) in H0.
            rewrite <- Nat.add_assoc in H0.
            rewrite <- Nat.mul_add_distr_l in H0.
            rewrite Nat.add_comm in H0.
            pose proof (divmod_correctness a m).
            destruct H6.
            apply H.
            pose proof (Nat.div_mod_unique m (b/m + x) (a / m) (b mod m) (a mod m)).
            destruct H8.
            assumption.
            assumption.
            rewrite <- H6. symmetry.
            assumption.
            rewrite H9. reflexivity.
            + intro. rewrite H3 in H0.
            apply Nat.sub_gt in H2.
            apply H2. assumption.
Qed.
                    
Lemma mod_add_from_lib:
    ∀ a b n : nat, n ≠ 0 → (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
    intros.
    pose proof (Nat.lt_trichotomy (a + b) n).
    destruct H0.
    - apply mod_biger in H0 as H1.
    rewrite H1.
    assert (a < n).
    {   
        unfold lt in *. 
        transitivity (S (a + b)).
        - rewrite <- Nat.add_succ_l.
        apply Nat.le_add_r.
        - assumption.
    }
    assert (b < n).
    {   
        unfold lt in *. 
        transitivity (S (a + b)).
        - rewrite Nat.add_comm.
        rewrite <- Nat.add_succ_l.
        apply Nat.le_add_r.
        - assumption.
    }
    apply mod_biger in H2.
    apply mod_biger in H3.
    rewrite H2.
    rewrite H3.
    rewrite H1.
    reflexivity.
    - destruct H0.
        -- rewrite H0. rewrite mod_equal.
        symmetry. 
        destruct a.
            + rewrite zero_mod_n.
            simpl in *. rewrite H0.
            rewrite mod_equal.
            rewrite zero_mod_n. reflexivity.
            + destruct b.
                ++ rewrite zero_mod_n.
                rewrite Nat.add_0_r in *.
                rewrite H0.
                rewrite mod_equal.
                rewrite zero_mod_n.
                reflexivity.
                ++ Search (_ + _ = _ -> _).
                (* Nat.div_mod_unique talvez seja útil em
                outros teoremas *)
                assert (S a < n /\ S b < n).
                {
                    split.
                    - unfold lt. rewrite <- H0.
                    rewrite Nat.add_succ_r.
                    rewrite <- Nat.add_succ_l.
                    apply Nat.le_add_r.
                    - unfold lt. rewrite <- H0.
                    rewrite Nat.add_comm.
                    rewrite Nat.add_succ_r.
                    rewrite <- Nat.add_succ_l.
                    apply Nat.le_add_r.  
                }
                destruct H1.
                apply mod_biger in H1.
                apply mod_biger in H2.
                rewrite H1.
                rewrite H2.
                rewrite H0.
                rewrite mod_equal.
                reflexivity.
        -- pose proof (Nat.lt_trichotomy (a mod n + b mod n) n).
        destruct H1.
            + apply mod_biger in H1 as H2.
            rewrite mod_meaning_full.
                ++ split.
                    * pose proof (divmod_correctness a n).
                    pose proof (divmod_correctness b n).
                    destruct H3. assumption.
                    destruct H4. assumption.
                    rewrite H3 at 1.
                    rewrite H4 at 1.
                    rewrite <- Nat.add_assoc.
                    rewrite (Nat.add_assoc (a mod n)).
                    rewrite (Nat.add_comm (a mod n)).
                    rewrite <- Nat.add_assoc.
                    rewrite Nat.add_assoc.
                    rewrite Nat.add_sub.
                    unfold divides.
                    exists ((a/n) + (b/n)).
                    rewrite Nat.mul_add_distr_l.
                    reflexivity.
                    * assert (a mod n + b mod n <= (a + b)).
                    {
                        unfold lt in *. transitivity n.
                        - transitivity (S (a mod n + b mod n)).
                            -- apply le_S. apply le_n.
                            -- assumption.
                        - transitivity (S n).
                            -- apply le_S. apply le_n.
                            -- assumption.   
                    }
                    apply Nat.sub_0_le in H3.
                    rewrite H3.
                    exists 0.
                    rewrite Nat.mul_0_r.
                    reflexivity.
                ++ assumption.
            + destruct H1.
            (* a mod n + b mod n = n *)
            rewrite H1.
            pose proof (divmod_correctness a n).
            pose proof (divmod_correctness b n).
            destruct H2.
            assumption.
            destruct H3.
            assumption.
            rewrite mod_meaning_full.
            split.
                ++ rewrite Nat.mod_eq in H1.
                rewrite Nat.mod_eq in H1.
                rewrite Nat.add_sub_assoc in H1.
                apply Nat.add_sub_eq_nz with (p := n) in H1.
                symmetry in H1.
                rewrite Nat.add_comm in H1.
                rewrite Nat.add_sub_assoc in H1.
                apply Nat.add_sub_eq_nz with (p := n * (b / n) + n) in H1.
                symmetry in H1.
                rewrite Nat.add_comm in H1.
                rewrite <- Nat.mul_succ_r in H1.
                rewrite <- Nat.mul_add_distr_l in H1.
                rewrite H1.
                exists (a / n + (b / n)).
                rewrite Nat.mul_add_distr_l.
                rewrite Nat.mul_succ_r.
                rewrite Nat.add_assoc.
                rewrite Nat.add_sub.
                rewrite Nat.mul_add_distr_l.
                reflexivity.
                destruct n.
                    * exfalso. apply H. reflexivity.
                    * intro. rewrite Nat.add_succ_r in H6.
                    discriminate.
                    * apply Nat.mul_div_le. assumption.
                    * assumption.
                    * apply Nat.mul_div_le. assumption.
                    * assumption.
                    * assumption.
                ++ unfold lt in H0.
                apply le_Sn_le in H0.
                apply Nat.sub_0_le in H0.
                rewrite H0.
                exists 0. rewrite Nat.mul_0_r.
                reflexivity.
                ++ assumption.
                ++ rewrite mod_meaning_full.
                split.
                    * pose proof (divmod_correctness a n).
                    pose proof (divmod_correctness b n).
                    destruct H2.
                    assumption.
                    destruct H3.
                    assumption.
                    rewrite H2 at 1.
                    rewrite H3 at 1.
                    rewrite <- Nat.add_assoc.
                    rewrite (Nat.add_assoc (a mod n)).
                    rewrite (Nat.add_comm (a mod n)).
                    rewrite <- Nat.add_assoc.
                    rewrite Nat.add_assoc.
                    rewrite Nat.add_sub.
                    rewrite <- Nat.mul_add_distr_l.
                    exists ((a/n) + (b/n)).
                    reflexivity.
                    * rewrite Nat.mod_eq.
                    rewrite Nat.mod_eq.
                    rewrite Nat.add_sub_assoc.
                    rewrite <- Nat.sub_add_distr.
                    rewrite (Nat.add_comm (n * (b/n))).
                    rewrite (Nat.add_comm a b).
                    rewrite Nat.sub_add_distr.
                    rewrite Nat.sub_add_distr.
                    rewrite <- Nat.add_sub_assoc.
                    rewrite Nat.sub_diag.
                    rewrite Nat.add_0_r.
                    rewrite <- Nat.sub_add_distr.
                    rewrite <- Nat.sub_add_distr.
                    rewrite Nat.add_assoc.
                    rewrite (Nat.add_comm _ a).
                    rewrite Nat.sub_add_distr.
                    rewrite Nat.sub_add_distr.
                    rewrite Nat.sub_diag.
                    simpl. exists 0.
                    rewrite Nat.mul_0_r.
                    reflexivity.
                    apply le_n.
                    apply Nat.mul_div_le.
                    assumption.
                    assumption.
                    assumption.
                    * assumption.
Qed.

Lemma mod_is_zero:
    ∀ a b : nat, b <> 0 -> a mod b = 0 -> b ∣ a.
Proof.
    intros. destruct b.
    - exfalso. apply H. reflexivity.
    - unfold Nat.modulo in H0.
    destruct (Nat.divmod a b 0 b) eqn:Case1.
    simpl in H0. 
    pose proof (Nat.divmod_spec a b 0 b).
    rewrite Case1 in H1.
    destruct H1.
        -- apply le_n.
        -- rewrite Nat.mul_0_r in H1.
        rewrite Nat.sub_diag in H1.
        repeat rewrite Nat.add_0_r in H1.
        rewrite H0 in H1.
        rewrite Nat.add_0_r in H1.
        rewrite H1.
        exists n. reflexivity.
Qed.

Lemma divmod_leq:
    ∀ a b, b * (a / b) <= a.
Proof.
    intros. pose proof (divmod_correctness a b).
    destruct b.
    - simpl. apply Nat.le_0_l.
    - destruct H.
        -- intro. discriminate.
        -- rewrite H at 2. apply Nat.le_add_r.
Qed.

Lemma mod_add:
    ∀ a b c m : nat, a mod m = b mod m -> 
    (a + c) mod m = (b + c) mod m.
Proof.
    intros.
    destruct m.
    - reflexivity.
    - apply mod_meaning_full in H. 
    destruct H. apply mod_meaning_full.
        -- intro. discriminate.
        -- split.
            + rewrite (Nat.add_comm b).
            rewrite Nat.sub_add_distr.
            rewrite Nat.add_sub. assumption.
            + rewrite (Nat.add_comm a).
            rewrite Nat.sub_add_distr.
            rewrite Nat.add_sub. assumption.
        -- intro. discriminate.
Qed. 

Lemma mod_multiple:
    ∀ a x : nat, (a * x) mod x = 0.
Proof.
    intros. intros. 
    generalize dependent x.
    induction a.
    - simpl. intros. rewrite zero_mod_n.
    reflexivity.
    - intros. specialize (IHa x). simpl.
    destruct x.
        -- reflexivity.
        -- rewrite mod_add_from_lib.
        rewrite IHa. rewrite mod_equal. simpl.
        rewrite Nat.sub_diag. reflexivity.
        intro. discriminate.
Qed.

Lemma gcd_multiple:
    ∀ a x : nat, Nat.gcd (a * x) x = x.
Proof.
    intros. generalize dependent x.
    induction a using strong_induction.
    intros. destruct x.
        - simpl. rewrite Nat.mul_0_r. reflexivity.
        - rewrite Nat.gcd_comm. rewrite Euclides.
        rewrite mod_multiple. simpl. reflexivity.
        intro. discriminate.
Qed.

Lemma mod_over:
    ∀ a b, (a mod b) mod b = a mod b.
Proof.
    intros. assert (a mod b = a mod b + 0 mod b).
    {
        rewrite zero_mod_n. rewrite Nat.add_0_r.
        reflexivity.   
    }
    destruct b.
        - reflexivity.
        - rewrite H at 1.
        rewrite <- mod_add_from_lib.
        rewrite Nat.add_0_r.
        reflexivity.
        intro. discriminate.
Qed.

Lemma gcd_add:
    ∀ a b m : nat, a <> 0 ->
    Nat.gcd (a + m * b) b = Nat.gcd a b.
Proof.
    intros.
    pose proof (Nat.lt_trichotomy a b).
    destruct H0.
        (* a < b *)
        - rewrite Nat.gcd_comm.
        rewrite Euclides.
        rewrite mod_add_from_lib.
        rewrite mod_multiple.
        rewrite Nat.add_0_r.
        rewrite mod_over.
        apply mod_biger in H0. rewrite H0. reflexivity.
        intro. subst b. inversion H0.
        intro. subst b. inversion H0.
        - destruct H0.
        (* a = b *)
        rewrite H0.
        rewrite Nat.gcd_comm.
        rewrite Euclides.
        rewrite Nat.add_comm.
        rewrite Nat.mul_comm.
        rewrite <- Nat.mul_succ_r.
        rewrite Nat.mul_comm.
        rewrite mod_multiple.
        simpl. rewrite Euclides.
        rewrite mod_equal. simpl.
        reflexivity.
        intro. subst b. apply H. assumption.
        intro. subst b. apply H. assumption.
        (* b < a *)
        destruct b.
            -- rewrite Nat.gcd_comm. symmetry.
            rewrite Nat.gcd_comm. simpl.
            rewrite Nat.mul_0_r.
            rewrite Nat.add_0_r.
            reflexivity.
            -- 
            rewrite Nat.gcd_comm.
            rewrite Euclides.
            rewrite mod_add_from_lib.
            rewrite mod_multiple.
            rewrite Nat.add_0_r.
            rewrite mod_over.
            symmetry.
            rewrite Nat.gcd_comm.
            rewrite Euclides.
            reflexivity.
            intro. discriminate.
            intro. discriminate.
            intro. discriminate.
Qed.

Lemma eq_less_plus:
    ∀ a b, a < b -> ∃ x c, b = c * a + x.
Proof.
    intros. exists (b - a). exists 1.
    rewrite Nat.mul_1_l.
    rewrite Nat.add_sub_assoc.
    rewrite Nat.add_comm.
    rewrite Nat.add_sub.
    reflexivity.
    unfold lt in H. transitivity (S a).
    - apply le_S. apply le_n.
    - assumption.
Qed.

Search (Nat.gcd).

Lemma gcd_prod:
    ∀ a b m, Nat.gcd (m * a) (m * b) = m * Nat.gcd a b.
Proof.
    intros.
    destruct m.
    simpl. reflexivity.
    (* pose proof (Nat.lt_trichotomy a b). *)
    (* destruct H. *)
    destruct a.
        - rewrite Nat.mul_0_r. simpl. reflexivity.
        - generalize dependent a.
        generalize dependent m.
        induction b using strong_induction.
        intros.
        pose proof (Nat.lt_trichotomy (S a) b). 
        destruct H0.
            -- rewrite Euclides. 
            symmetry. 
            rewrite Euclides. 
            rewrite Nat.mul_mod_distr_l.
            rewrite Nat.gcd_comm.
            symmetry.
            rewrite Nat.gcd_comm.
            apply H.
            apply mod_less.
            split.
            intro. subst b. inversion H0.
            transitivity (S a). apply le_n. assumption.
            intro. discriminate.
            intro. discriminate.
            intro. discriminate.
            simpl. intro. discriminate.
            -- destruct H0.
            (* S a = b *)
            subst b.
            rewrite <- (Nat.mul_1_l (S m * S a)) at 1.
            rewrite gcd_multiple.
            symmetry.
            rewrite <- (Nat.mul_1_l (S a)) at 1.
            rewrite gcd_multiple.
            reflexivity.
            (* b < S a *)
            destruct b.
                + rewrite Nat.gcd_comm.
                symmetry. rewrite Nat.gcd_comm.
                rewrite Nat.mul_0_r.
                simpl. reflexivity.
                + 
                (* induction (S a) using strong_induction. *)
                pose proof (divmod_correctness (S a) (S b)).
                destruct H1.
                intro. discriminate.
                rewrite H1 at 1.
                rewrite Nat.add_comm.
                rewrite Nat.mul_add_distr_l.
                rewrite Nat.mul_assoc.
                rewrite (Nat.mul_comm (S m * S b) _) at 1.
                destruct ((S a) mod (S b)) eqn:Case1.
                    ++ rewrite Nat.mul_0_r.
                    rewrite Nat.add_0_l.
                    rewrite Nat.gcd_comm.
                    rewrite Euclides.
                    rewrite mod_multiple.
                    symmetry.
                    rewrite Nat.gcd_comm.
                    rewrite Euclides.
                    rewrite Nat.add_0_r in H1.
                    rewrite H1.
                    rewrite (Nat.mul_comm (S b) _).
                    rewrite mod_multiple.
                    simpl. reflexivity.
                    intro. discriminate.
                    simpl. intro. discriminate.
                    ++ rewrite gcd_add.
                    symmetry.
                    rewrite H1 at 1.
                    rewrite Nat.add_comm.
                    rewrite (Nat.mul_comm (S b) _).
                    rewrite gcd_add.
                    rewrite Nat.gcd_comm.
                    symmetry.
                    rewrite Nat.gcd_comm.
                    apply H.
                    assumption.
                    intro. discriminate.
                    simpl. intro. discriminate.
Qed.  

Lemma gcd_divides_l:
    ∀ a b, (Nat.gcd a b) ∣ a.
Proof.
    intros.
    - generalize dependent a. 
    induction b using strong_induction.
    intros.
    pose proof (Nat.lt_trichotomy b a).
    destruct H0.
        -- destruct a.
            + simpl. exists 0.
            rewrite Nat.mul_0_r. reflexivity.
            + destruct b.
            (* b = 0 *)
            rewrite Nat.gcd_comm. simpl.
            exists 1. rewrite Nat.mul_1_r.
            reflexivity.
            (* S b *)
            pose proof (divmod_correctness (S a) (S b)).
            destruct H1.
            intro. discriminate.
            rewrite H1 at 2.
            rewrite gcd_comm.
            rewrite Euclides.
            rewrite gcd_comm.
            specialize (H (S a mod S b)) as H3.
            apply H3 with (a0 := (S b)) in H2 as H4.
            assert ((Nat.gcd (S b) (S a mod S b)) ∣ ((S b) * (S a / S b))).
            {
             unfold divides in H4. destruct H4.
             unfold divides.
             exists (x * (S a / S b)).
             rewrite Nat.mul_assoc.
             rewrite <- H4. reflexivity.   
            }
            specialize (H (S a)).
            apply H3 with (a0 := (S b) + (S a mod S b)) in H2.
            rewrite <- (Nat.mul_1_l (S a mod S b)) in H2 at 1.
            rewrite gcd_add in H2.
            assert ((Nat.gcd (S b) (S a mod S b)) ∣ (S a mod S b)).
            {
                unfold divides.
                destruct H2.
                destruct H4.
                exists (x - x0).
                rewrite Nat.mul_sub_distr_l.
                rewrite <- H2.
                rewrite <- H4.
                rewrite Nat.add_comm.
                rewrite Nat.add_sub.
                reflexivity.
            }
            destruct H5.
            destruct H6.
            exists (x + x0).
            rewrite Nat.mul_add_distr_l.
            rewrite <- H5.
            rewrite <- H6. reflexivity.
            intro. discriminate.
            intro. discriminate.
        -- destruct H0.
            + subst b.
            destruct a.
                ++ simpl. exists 1. reflexivity.
                ++ rewrite Euclides.
                rewrite mod_equal.
                simpl. exists 1. rewrite Nat.mul_1_r.
                reflexivity.
                intro. discriminate.
            + destruct a.
                ++ simpl. exists 0. rewrite Nat.mul_0_r.
                reflexivity.
                ++ rewrite Euclides.
                rewrite Nat.gcd_comm.
                pose proof (divmod_correctness b (S a)).
                destruct H1. intro. discriminate.
                apply H. transitivity (S a).
                assumption.
                assumption.
                intro. discriminate.
Qed.

Lemma gcd_divides:
    ∀ a b, (Nat.gcd a b) ∣ a /\ (Nat.gcd a b) ∣ b .
Proof.
    intros. split.
    - apply gcd_divides_l.
    - rewrite gcd_comm. apply gcd_divides_l. 
Qed.

Lemma gcd_greatest:
    ∀ a b c, c ∣ a /\ c ∣ b -> c ∣ (Nat.gcd a b).
Proof.
    intros.
    destruct H. destruct H. destruct H0 as [y].
    remember (Nat.gcd a b) as n.
    subst a. subst b.
    rewrite gcd_prod in Heqn.
    exists (Nat.gcd x y).
    assumption.
Qed.

Lemma divides_itself:
    ∀ a b, a ∣ b /\ b ∣ a <-> a = b.
Proof.
    intro. split.
    - intros. destruct H.
    destruct H. destruct H0.
    rewrite H0 in H.
    destruct b.
        -- simpl in H0. assumption.
        --
    assert (x0 * x = 1 \/ x0 * x = 0).
    {
      destruct (x0 * x) eqn:Case.
      right. reflexivity.
      
      rewrite <- Nat.mul_assoc in H.
      rewrite Case in H.
      rewrite Nat.mul_succ_r in H.
      rewrite Nat.add_comm in H.
      apply eq_add_0 in H.
      apply mult_is_O in H.
      destruct H.
      discriminate.
      left. subst n. reflexivity.
    }
    destruct H1.
    Search (_ * _ = 1).
    apply mult_is_one in H1.
    destruct H1. subst x0. subst x.
    rewrite Nat.mul_1_r in H0.
    assumption.
    apply mult_is_O in H1.
    destruct H1.
    subst x0.
    rewrite Nat.mul_0_r in H.
    simpl in H.
    discriminate.
    subst x.
    rewrite Nat.mul_0_r in H.
    discriminate.
    - intros. split.
        -- rewrite H. exists 1. rewrite Nat.mul_1_r.
        reflexivity.
        -- rewrite H. exists 1. rewrite Nat.mul_1_r.
        reflexivity. 
Qed.

Lemma divisor_is_leq:
    ∀ a b, a ∣ b /\ b <> 0 -> a <= b.
Proof.
    intros. generalize dependent b.
    induction a.
    - intros. apply Nat.le_0_l.
    - intros. destruct H.
    destruct H. rewrite H.
    destruct x.
        -- rewrite Nat.mul_0_r in H. exfalso.
        apply H0. assumption.
        -- rewrite Nat.mul_succ_r.
        rewrite Nat.add_comm.
        apply Nat.le_add_r.
Qed.


(* Prova final do corretude do algoritmo de Euclides *)
Theorem correctness_gcd: 
    ∀ a b n, Nat.gcd a b = n <-> gcd a b n.
Proof.
    intros. split.
    - intros. unfold gcd. split.
        -- pose proof (gcd_divides a b).
        destruct H0.
        subst n. assumption.
        -- split.
        pose proof (gcd_divides a b).
        destruct H0.
        subst n. assumption.
        intro.
        subst n.
        apply gcd_greatest.
    - intro. unfold gcd in H.
    destruct H.
    destruct H0.
    specialize (H1 (Nat.gcd a b)) as H2.
    pose proof (gcd_divides a b).
    apply H2 in H3.
    pose proof (gcd_greatest a b n).
    assert ((n) ∣ (Nat.gcd a b)).
    {
     apply H4.
     split.
     assumption.
     assumption.   
    }
    apply divides_itself.
    split.
    assumption.
    assumption.
Qed.

End ToyPlayground.

Module ProvenStuff.

Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Fixpoint sumdigits n (f : nat -> Z) :=
  match n with
  | O => f O
  | S n => f (S n) + sumdigits n f
  end.

Fixpoint number n (f : nat -> Z) :=
  match n with
  | O => f O
  | S n => f (S n) + 10 * number n f
  end.

Theorem div3 : forall n d,
  (number n d) mod 3 = (sumdigits n d) mod 3.
Proof.
  intros n d; induction n.
  - simpl. reflexivity.
  - change ((d (S n) + 10 * number n d) mod 3 = (d (S n) + sumdigits n d) mod 3).
    rewrite Zplus_mod, Zmult_mod, IHn.
    remember (sumdigits n d) as SU.
    replace (10 mod 3) with 1 by trivial.
    rewrite Zmult_1_l, Zmod_mod.
    rewrite <- Zplus_mod.
    reflexivity.
Qed.

End ProvenStuff.


(* Module ToyWithPairIntegers.

Require Import Coq.Numbers.Integer.NatPairs.ZNatPairs.

Compute (Z.a    dd 1 2).



End ToyWithSetsIntegers. *)

(* Aqui vamos provar o algoritmo de Euclides
estendido *)
Module ToyWithIntegers.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Wf.
Require Import Wellfounded.
Require Import ZArith Coq.ZArith.Znumtheory.
Require Import ZArith.Zwf.
Require Import PeanoNat.
Require Import Lia.

Print Z.gcd.

Program Fixpoint euclids' (a b: Z) {measure (Z.abs_nat (Z.abs a))} : Z * Z * Z :=
  if Z.eq_dec a (0)%Z then (b, (0)%Z, (1)%Z)
  else let '(g, s, t) := euclids' (b mod a) a in
       (g, ((t - (Z.div b a)%Z)%Z * s)%Z, s).
Next Obligation.
apply Zabs_nat_lt. split. apply Z.abs_nonneg. apply Z.mod_bound_abs. assumption. 
Defined.

Program Fixpoint Euclides_Ext (a b : Z) 
    {measure (Z.abs_nat (Z.abs b))} :=
    match b with
        | 0 => (a, 1, 0)
        | _ => let '(g, x', y') := Euclides_Ext b (a mod b)
        in (g, y', x' - (a/b) * y')
    end.    
Next Obligation.
    apply Zabs_nat_lt. split.
    - apply Z.abs_nonneg.
    - pose proof (Z.mod_bound_abs a b). apply H0.
    intro. subst b. apply H. reflexivity.
Defined.

Compute (Euclides_Ext 2 9).

(* ∀ a b, a <> 0 -> Nat.gcd a b = Nat.gcd (b mod a) a *)

Print Z.pred.

Definition dist (m n : Z) :=
    Z.abs (m - n).

Lemma dist_comm:
    ∀ m n, dist m n = dist n m.
Proof.
    intros. unfold dist.
    rewrite <- Z.abs_opp.
    rewrite Z.opp_sub_distr.
    rewrite Z.add_opp_l.
    reflexivity.
Qed.

Lemma dist_diff_0:
    ∀ m n, n < m -> 0 < dist n m.
Proof.
    intros. unfold dist.
    Search (_ < _ -> 0 < _).
    apply Zlt_left_lt in H.
    Search (Z.abs).
    rewrite <- Z.abs_opp.
    Search (- (_ - _)).
    rewrite Z.opp_sub_distr.
    Search (- _ + _ = _).
    rewrite Z.add_opp_l.
    Search (_ + (- _) = _).
    rewrite Z.add_opp_r in H.
    destruct (m - n).
    - inversion H.
    - simpl. assumption.
    - inversion H.
Qed.

Theorem induction_integers (m: Z) (P: Z -> Prop):
  P m ->
  (forall j,
    (forall i, (dist i m < dist j m)%Z -> P i) -> P j) ->
  forall n,
  P n.
Proof.
  intros.
  remember (Z.to_nat (dist n m)) as d.
  generalize dependent n.
  induction d using lt_wf_ind. intros.
  destruct d.
  - unfold dist in Heqd.
    (* como Z.abs (n - m) = 0 então n = m *)
    assert (n = m) by lia.
    rewrite H2. assumption.
  - apply H0. intros.
    apply H1 with (Z.to_nat (dist i m)).
    + rewrite Heqd.
        (* pela hipótese H2 *)
        lia.
    + reflexivity.
Qed.

Theorem Euclides_Ext_Correctness:
    ∀ a b : Z, 
    a * (snd (fst (Euclides_Ext a b))) + b * (snd (Euclides_Ext a b)) = fst (fst (Euclides_Ext a b)).
Proof.
    intros. generalize dependent a.
    generalize dependent b.
    induction b using (induction_integers 0).
    - intros. simpl. lia.
    - intros. Search (Z.succ _).
        
Qed.



End ToyWithIntegers.