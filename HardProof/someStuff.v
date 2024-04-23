From LF Require Export Induction.
Require Export Arith.
From Coq Require Import Unicode.Utf8_core.

(*  Para compilar o que está listado no "_CoqProject":
     
    make -f Makefile 
    
    Para limpar o que foi compilado (depois disso não
    dá pra fazer Required a não ser que compile nova-
    mente): 
    
    make -f Makefile clean
    
    *)

Theorem contraposition: ∀ P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    intros. unfold not. intro. apply H in H1.
    apply H0 in H1. apply H1.
Qed.

Theorem contraposition_iff: ∀ P Q : Prop,
    (P <-> Q) -> (~P <-> ~Q).
Proof.
    intros. split.
    - intros. unfold not in H0. unfold not.
        intro. apply H in H1. apply H0 in H1.
        apply H1.
    - intros. unfold not in H0. unfold not.
        intro. apply H in H1. apply H0 in H1.
        apply H1.
Qed. 

Theorem false_diff_true:
    false <> true.
Proof.
    discriminate.
Qed.

Theorem true_diff_false:
    true <> false.
Proof.
    discriminate.
Qed.

Theorem diff_true_is_false: ∀ p : bool,
    p <> true <-> p = false.
Proof.
    intros. split.
    - intro. destruct p.
        -- destruct H. reflexivity.
        -- reflexivity.
    - intro. rewrite H. apply false_diff_true.
Qed.

Theorem diff_false_is_true: ∀ p : bool,
    p <> false <-> p = true.
Proof.
    intros. split.
    - intro. destruct p.
        -- reflexivity.
        -- destruct H. reflexivity.
    - intros. rewrite H. discriminate.
Qed. 


Theorem even_succ: ∀ n : nat,
    even (n+1) = true <-> even (n) = false.
Proof.
    intros. split.
    - intro. induction n as [|k].
        + simpl. discriminate.
        + apply contraposition in IHk.
            -- apply diff_true_is_false in IHk.
                rewrite add_comm in IHk.
                rewrite plus_1_l in IHk.
                apply IHk.
            -- rewrite add_comm in H.
                rewrite plus_1_l in H.
                simpl in H.
                rewrite H. discriminate.
    - intro. induction n as [|k].
        + simpl. simpl in H. symmetry in H. apply H.
        + apply contraposition in IHk.
            -- apply diff_false_is_true in IHk.
                rewrite add_comm. rewrite plus_1_l.
                simpl. apply IHk.
            -- rewrite add_comm. rewrite plus_1_l.
                rewrite H. discriminate.
Qed.             

Theorem plus_one_both_sides: ∀ n m : nat, 
    n = m -> n + 1 = m + 1.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Theorem less_one_both_sides: ∀ n m : nat,
    n = m -> n - 1 = m - 1.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Theorem nat_is_2i_or_2i_plus_one: ∀ n : nat,
    (∃ i : nat, n = 2 * i) \/ (∃ i : nat, n = 2 * i + 1).
Proof.
    intros. induction n as [|k].
    - left. exists 0. reflexivity.
    - destruct IHk.
        -- destruct H. apply plus_one_both_sides in H.
            rewrite add_comm in H. rewrite plus_1_l in H.
            right. exists x. apply H.
        -- destruct H. apply plus_one_both_sides in H.
            rewrite add_comm in H. rewrite plus_1_l in H.
            rewrite <- add_assoc' in H.
            simpl (1+1) in H.
            left. exists (x + 1).
            rewrite mul_comm.
            rewrite mult_plus_distr_r.
            simpl. rewrite mul_comm.
            apply H.
Qed.

Theorem diff_2i_eq_2i_plus_one: ∀ n : nat,
    ~(∃ i : nat, n = 2*i) -> ∃ i : nat, n = 2*i + 1.
Proof.
    intros. induction n as [|k].
    - destruct H. exists 0. reflexivity.
    - pose proof nat_is_2i_or_2i_plus_one.
        destruct H0 with (S k).
        -- apply H in H1. destruct H1.
        -- apply H1.
Qed.

(* Theorem is_2i_neg_2i_plus_one: ∀ n : nat,
    ∃ i : nat, n = 2*i -> ~(∃ i : nat, n = 2*i + 1.)  *)

Theorem plus_one_minus_one: ∀ n : nat,
    n + 1 - 1 = n.
Proof.
    intros. induction n as [|k].
    - simpl. reflexivity.
    - simpl. rewrite add_comm. rewrite plus_1_l. simpl. reflexivity.
Qed. 

Theorem add_sub_comm: ∀ n : nat, 
    (S n) + 1 - 1 = (S n) - 1 + 1.
Proof.
    intros. rewrite plus_one_minus_one.
    induction n as [|k].
    - simpl. reflexivity.
    - simpl. rewrite add_comm. replace (1 + k) with (S k).
        -- reflexivity.
        -- simpl. reflexivity.
Qed.

(* Theorem diff_2i_plus_one_eq_2i: ∀ n : nat,
    (∃ i : nat, n = 2*i + 1) -> ~(∃ m : nat, n = 2*m).
Proof.
    intros. induction n as [|k].
    - destruct H. rewrite add_comm in H. rewrite plus_1_l in H.
        discriminate H. 
    - destruct H. unfold not. intro. destruct H0.
        apply less_one_both_sides in H0.
        rewrite <- plus_1_l in H0. rewrite add_comm in H0.
        rewrite plus_one_minus_one in H0.
        rewrite <- plus_one_minus_one in H0.
        rewrite add_comm in H0.

Qed. *)

Fixpoint div2 (n:nat) : nat :=
  match n with
  | O => O
  | S O => O 
  | S (S n') => S (div2 n')  
end.

Theorem div2_both_sides: ∀ n m : nat, 
    (n = m) -> (div2 n) = (div2 m).
Proof.
    intros. rewrite H. reflexivity.
Qed. 

Theorem plus_two_double_succ: ∀ n : nat,
    n + 2 = S(S n).
Proof.
    intros. symmetry. rewrite <- plus_1_l.
    replace (S n) with (1 + n).
    - rewrite add_assoc. simpl (1 + 1). rewrite add_comm.
        reflexivity.
    - reflexivity.
Qed. 

Theorem mul2_eq_plus: ∀ n : nat,
    2 * n = n + n.
Proof.
    intros. simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem div2_mul2_eq: ∀ n : nat,
    n = div2 (2 * n).
Proof.
    intros. induction n as [|k].
    - simpl. reflexivity.
    - rewrite <- plus_1_l.
        rewrite <- mult_n_Sm. symmetry.
        rewrite plus_two_double_succ. simpl.
        rewrite add_0_r. rewrite <- mul2_eq_plus.
        rewrite <- IHk. reflexivity.
Qed.

Theorem one_diff_2i: ∀ i,
    ~(1 = 2 * i).
Proof.
    intros. intro. pose proof H as H'. apply div2_both_sides in H.
    simpl in H. rewrite add_0_r in H. 
    rewrite <- mul2_eq_plus in H. rewrite <- div2_mul2_eq in H.
    rewrite <- H in H'. simpl in H'. discriminate H'. 
Qed.

Theorem less_x_both_sides: ∀ n m x : nat,
    n = m -> n - x = m - x.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Theorem x_minus_x_is_0: ∀ x,
    x - x = 0.
Proof.
    intros. induction x as [|k].
    - simpl. reflexivity.
    - simpl. apply IHk.
Qed.



(* 
Theorem plus_x_minus_x: ∀ n x : nat,
    n + x - x = n.
Proof.
    intros. induction x as [|k].
    - rewrite add_0_r. assert (n - 0 = n).
    {
        induction n as [|k].
        - simpl. reflexivity.
        - simpl. reflexivity.
    }
    apply H.
    - rewrite <- plus_1_l. *)

(* Lembre-se de fazer unfold not e unfold, é um caminho que existe
    quando parece não haver mais nenhum *)

Theorem succ_2i_pred_2i_plus_one: ∀ n : nat,
    (∃ i : nat, (S n) = 2 * i) -> ∃ m : nat, n = 2 * m + 1.
Proof.
    intros. induction n as [|k].
    - destruct H. pose proof one_diff_2i. destruct H0 with x. apply H.
    - pose proof nat_is_2i_or_2i_plus_one. 
        destruct H0 with k.
        -- destruct H1.
            apply plus_one_both_sides in H1.
            rewrite add_comm in H1 at 1.
            rewrite plus_1_l in H1.
            exists x. apply H1.
        -- destruct H.
            exists (x-1).
            simpl.
            rewrite add_0_r.
            rewrite <- add_assoc.
            destruct x.
                --- simpl. simpl in H.
                    discriminate H.
                --- simpl. assert (x - 0 = x).
                {
                 destruct x.
                 - simpl. reflexivity.
                 - simpl. reflexivity.   
                }
                rewrite H2.
                rewrite <- plus_1_l in H.
                rewrite add_comm in H.
                apply less_one_both_sides in H.
                rewrite plus_one_minus_one in H.
                assert (2 * S x = S(S (2 *x))).
                {
                 simpl. rewrite add_0_r.
                 rewrite <- plus_n_Sm. reflexivity.  
                }
                rewrite H3 in H.
                simpl in H. rewrite add_0_r in H.
                rewrite H.
                rewrite plus_n_Sm. 
                rewrite <- plus_1_l.
                symmetry.
                rewrite add_comm.
                rewrite add_assoc.
                reflexivity.
Qed.

Theorem mult_2_n_plus : forall (n : nat),
  n + n = 2 * n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite add_0_r.
    reflexivity.
Qed.

Theorem mul2_div2 : forall n : nat,
  n = div2 (2 * n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite <- plus_1_l.
    rewrite <- mult_n_Sm.
    rewrite plus_two_double_succ.
    simpl. rewrite add_0_r.
    rewrite mult_2_n_plus.
    rewrite <- IHn.
    reflexivity.
Qed.

(*Theorem div2_mult2_plus: forall (n m : nat),
  n + div2 m = div2 (2 * n + m).
Proof.
  intros n m.
  induction n.
  - reflexivity.
  -  
Qed.*)

Theorem minus_zero: ∀ m : nat,
    m - 0 = m.
Proof.
    intros. induction m as [|k].
    - simpl. reflexivity.
    - simpl. reflexivity. 
Qed.

Search (_ <= S _).
(* Nat.lt_le_incl: ∀ n m : nat, n < m → n <= m *)
(* Nat.le_pred_le_succ: ∀ n m : nat, Nat.pred n <= m ↔ n <= S m *)

Theorem lessEq_implies_then_less_implies (P : nat -> Prop) :
    ∀ m n : nat, (m <= n → P n ) -> (m < n -> P n).
Proof.
    intros. assert (m < n -> m <= n). 
        {
            intros. apply Nat.lt_le_incl. apply H1. 
        }
    apply H1 in H0.
    apply H in H0. apply H0.
Qed.

(* Perguntar para o professor por que não há quantificador sobre a pre-
posição P *)
Theorem m_less_than_n_implies (P : nat -> Prop) : 
    ∀ n m : nat, (m < n) -> (P(n)) <-> P(n).
Proof.
    intros. reflexivity.    
Qed.

Theorem if_B_then_A_implies_B: ∀ A B : Prop,
    B -> (A -> B).
Proof.
    intros. apply H.
Qed.

(* Por que o teorema acima quando aplicado em B leva para o próprio B,
 e não para A -> B que é o que preciso? *)
(* Theorem implies_true_implies: forall A B C : Prop,
    (B /\ ((A -> B) -> C)) -> C.
Proof.
    intros. destruct H. 
    pose proof if_B_then_A_implies_B.
    specialize (H1 A B).
    apply H1 in H.
    - apply H0. apply H1. apply H.
    - pose proof if_B_then_A_implies_B.
Qed.

Lemma strong_ind (P : nat -> Prop) :
  ∀ m : nat, (P (m) /\ (∀ k : nat, ((m < k) -> P(k)) -> P(S k))) -> forall n : nat,(m <= n -> P(n)).
Proof.
    intro. intros. destruct H. induction n.
    - specialize H1 with 0. destruct m.
        -- apply H.
        -- inversion H0.
    - specialize H1 with n.  apply lessEq_implies_then_less_implies in IHn.

Qed. *)

Theorem two_a_is_not_two_b_plus_one: ∀ n m : nat, 
    2 * n <> 2 * m + 1.
Proof.
    intros. generalize dependent n. induction m as [|k].
    - intros. unfold not. intros. simpl in H. rewrite add_0_r in H.
    destruct n.
        -- simpl in H. discriminate H.
        -- rewrite <- plus_n_Sm in H. injection H.
        intros. discriminate H0.
    - intros. unfold not in *. intros. apply IHk with (n := n). 
Qed.


Theorem is_2i_plus_one_neg_2i: ∀ n : nat,
    (∃ i : nat, n = 2 * i + 1) -> ~(∃ k : nat, n = 2 * k).
Proof.
    intros. unfold not. intros. destruct H. destruct H0.
    pose proof H0 as H1. rewrite H in H0.
    apply div2_both_sides in H0.
    rewrite <- div2_mul2_eq in H0.
    rewrite <- H0 in H1.
    rewrite H1 in H.
    

Theorem succ_not_even: ∀ n : nat,
    even (n) = true -> even (S n) = false.
Proof.
    intros. induction n as [|k].
    - simpl. reflexivity.
    - simpl. apply contraposition in IHk.
        -- apply diff_true_is_false in IHk. apply IHk.
        -- rewrite diff_false_is_true. apply H.
Qed.

Theorem succ_is_even: ∀ n : nat,
    even (n) = false -> even (S n) = true.
Proof.
    intros. induction n as [|k].
    - simpl in H. simpl. rewrite H. reflexivity.
    - simpl. apply contraposition in IHk.
        -- apply diff_false_is_true in IHk. apply IHk.
        -- apply diff_true_is_false. apply H.  
Qed.

Theorem even_classic_def: ∀ n : nat,
    even (n) = true <-> ∃ i : nat, n = 2 * i.
Proof.
    intros. induction n as [|k].
    - split.
        -- intro. exists 0. reflexivity.
        -- intro. simpl. reflexivity.
    - split.
        -- intro.
        pose proof nat_is_2i_or_2i_plus_one.
        destruct H0 with (S k).
            --- apply H1.
            --- destruct H1. rewrite <- plus_1_l in H1.
                rewrite add_comm in H1. 
                apply less_one_both_sides in H1.
                rewrite plus_one_minus_one in H1.
                symmetry in H1.
                rewrite plus_one_minus_one in H1.
                symmetry in IHk.
                symmetry in H1.
                assert (even k = true).
                    {
                        apply IHk. exists x. apply H1.
                    }
                apply succ_not_even in H2. rewrite H in H2. 
                discriminate H2.
        -- intros. destruct H. destruct IHk.
            rewrite <- plus_1_l. rewrite add_comm.
            rewrite even_succ.
            apply contraposition in H0.
            --- rewrite diff_true_is_false in H0. apply H0.
            --- 
Qed.

Theorem not_even_classic_def: ∀ n : nat,
    even (n) = false <-> ~(∃ i : nat, n = 2 * i).
Proof.
    intros. split.
    - intro. destruct n.
