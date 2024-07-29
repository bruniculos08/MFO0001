Require Export Arith.
Require Export PeanoNat.
From Coq Require Import Unicode.Utf8_core.

Definition multiple (a b : nat) :=
    ∃ q : nat, (a = b * q).

Definition divides (a b : nat) :=
    ∃ q : nat, b = a * q.

Notation "a ∣ b" := (divides a b) (at level 0, right associativity).

Definition Even (n : nat) :=
    ∃ m : nat, (n = 2 * m).

Theorem Even_multiple_two: ∀ n : nat, 
    Even n -> multiple n 2.
Proof.
    intros. unfold Even in *. unfold multiple. destruct H.
    exists x. apply H.
Qed.

Definition Odd (n : nat) :=
    ∃ m : nat, (n = 2 * m + 1).

Theorem Odd_or_Even:
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

Fixpoint odd (n : nat) : bool :=
    match n with
    | 0 => false
    | 1 => true
    | S (S n) => odd n
    end.

Definition notb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
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
    - intros. unfold not in H. pose proof Odd_or_Even. specialize (H0 n).
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
    - intros. pose proof Odd_or_Even. specialize (H0 n). destruct H0.
        -- apply H0.
        -- apply H in H0. destruct H0. 
Qed.

Lemma Even_succ_then_not_Even:
    ∀ n : nat, Even (S n) <-> ~ Even n.
Proof.
    intros. split. 
    - intros. induction n as [|k].
    -- destruct H. destruct x.
        --- simpl in H. discriminate H.
        --- simpl in H. rewrite Nat.add_succ_r in H. discriminate H.
    -- intro. unfold Even in *. apply IHk in H0. unfold not in H0.
    apply H0. destruct H. destruct x.
        --- simpl in H. discriminate H.
        --- simpl in H. rewrite Nat.add_succ_r in H. injection H.
        intros. exists x. simpl. apply H1.
    - intros. apply Odd_eq_not_Even in H. unfold Odd in H. destruct H.
    exists (x + 1). rewrite H. simpl. rewrite Nat.add_0_r. rewrite Nat.add_0_r.
    rewrite Nat.add_1_r. rewrite Nat.add_1_r. simpl.
    Search (_ + S _). rewrite plus_n_Sm. reflexivity.
Qed.

Lemma even_n_odd_succ: 
    ∀ n : nat, even n = true <-> even (S n) = false.
Proof.
    intros. induction n as [|k].
    - split.
        -- intros. simpl. reflexivity.
        -- intros. simpl. reflexivity.
    - split.
        -- intros. simpl. destruct (even k).
            + rewrite <- H. apply IHk. reflexivity.
            + reflexivity.
        -- intros. simpl in H. destruct (even (S k)).
            + reflexivity.
            + rewrite <- H. apply IHk. reflexivity.
Qed.

Lemma odd_n_even_succ: 
    ∀ n : nat, odd n = true <-> odd (S n) = false.
Proof.
    intros. split.
    - intros. induction n.
        -- simpl in H. discriminate H.
        -- simpl. destruct (odd n).
            + rewrite H in IHn. apply IHn. reflexivity.
            + reflexivity.
    - intros. induction n.
        -- simpl in H. discriminate H.
        -- destruct (odd (S n)).
            + reflexivity.
            + simpl in H. rewrite H in IHn. apply IHn. reflexivity. 
Qed.

Lemma odd_eq_not_even:
    ∀ n : nat, odd n = notb (even n).
Proof.
    induction n.
    - simpl. reflexivity.
    - pose proof odd_n_even_succ. pose proof even_n_odd_succ.
        + destruct (even (S n)) eqn:Case.
            -- simpl (notb true). apply H. destruct (odd n).
                ++ reflexivity.
                ++ symmetry. rewrite <- Case. apply H0.
                destruct (even n).
                    --- reflexivity.
                    --- simpl in IHn. discriminate IHn.
            -- simpl (notb (false)). apply H0 in Case. rewrite Case in IHn.
            simpl in IHn. specialize (H (S n)). simpl (odd (S (S n))) in H.
            apply H in IHn. apply IHn.
Qed.        

Lemma even_eq_not_odd:
    ∀ n : nat, even n = notb (odd n).
Proof.
    intros. destruct (even n) eqn:Case. rewrite odd_eq_not_even.
    rewrite Case. simpl. reflexivity.
    rewrite odd_eq_not_even. rewrite Case. simpl. reflexivity.
Qed.

Lemma contra_position: 
    ∀ A B : Prop, (A -> B) -> (~ B -> ~ A).
Proof.
    intros. intro. unfold not in H0. apply H0. apply H. apply H1.
Qed.

Lemma bi_contra_position:
    ∀ A B, (A <-> B) -> (~ A <-> ~ B).
Proof.
    intros. destruct H. split.
    - intros. intro. apply H0 in H2. apply H1 in H2. apply H2.
    - intros. intro. apply H1. apply H. apply H2.
Qed.

Lemma exclude_Even_succ:
    ∀ n : nat, ~ (Even n /\ Even (S n)).
Proof.
    intros. intro. destruct H. induction n.
    - unfold Even in *. destruct H. destruct H0.
        -- destruct x0.
            + simpl in H0. discriminate H0.
            + simpl in H0. rewrite Nat.add_succ_r in H0. discriminate H0.
    - apply IHn.
        -- destruct H0. destruct x.
            + discriminate H0.
            + simpl in H0. rewrite Nat.add_succ_r in H0. injection H0.
            intros. unfold Even. exists x. simpl. apply H1.
        -- apply H.
Qed.

Lemma notb_arg:
    ∀ x y, notb x = y <-> x = notb y.
Proof.
    intros. destruct x. destruct y.
    - simpl. split.
        -- intro. discriminate H.
        -- intro. discriminate H.
    - simpl. split.
        -- intro. reflexivity.
        -- intro. reflexivity.
    - simpl. split.
        -- intro. rewrite <- H. simpl. reflexivity.
        -- intro. destruct y.
            + reflexivity.
            + simpl in H. discriminate H.
Qed.

Lemma And_intro:
    ∀ A B : Prop, A -> B -> A /\ B.
Proof.
    intros. split. apply H. apply H0.
Qed.

Lemma not_even_then_odd:
    ∀ n : nat, ∀ b : bool, ~ (even n = b) <-> odd n = b.
Proof.
    intros. split.
    - intro. unfold not in H. induction n as [|k].
        -- simpl in H. destruct b.
            + exfalso. apply H. reflexivity.
            + simpl. reflexivity.
        -- destruct b. pose proof even_eq_not_odd. destruct (odd (S k)) eqn:Case.
            + reflexivity.
            + exfalso. apply H. pose proof even_n_odd_succ. apply H1. apply H1.
            rewrite H0. rewrite notb_arg. simpl (notb true). apply Case.
            + destruct (even k) eqn:CaseEven.
                ++ exfalso. apply H. rewrite even_n_odd_succ in CaseEven. apply CaseEven.
                ++ rewrite even_eq_not_odd in CaseEven. rewrite notb_arg in CaseEven.
                simpl in CaseEven. rewrite odd_n_even_succ in CaseEven. apply CaseEven.
    - intros. unfold not. intro. induction n as [|k].
        -- simpl in *. destruct b.
            + discriminate H.
            + discriminate H0.
        -- destruct b.
            + apply IHk.
                ++ rewrite even_n_odd_succ in H0. rewrite even_eq_not_odd in H0.
                rewrite notb_arg in H0. simpl in H0. apply H0.
                ++ rewrite odd_n_even_succ in H. rewrite odd_eq_not_even in H.
                rewrite notb_arg in H. simpl in H. apply H.
            + apply IHk.
                ++ rewrite even_eq_not_odd in H0. rewrite notb_arg in H0.
                simpl (notb false) in H0. rewrite odd_n_even_succ in H0.
                simpl in H0. apply H0.
                ++ rewrite odd_eq_not_even in H. rewrite notb_arg in H.
                simpl (notb false) in H. rewrite even_n_odd_succ in H.
                simpl in H. apply H.
Qed.

Theorem even_classic_def: 
    ∀ n : nat, (even n) = true <-> Even n.
Proof.
    pose proof even_n_odd_succ. induction n as [|k].
    - simpl. split.
        -- intros. exists 0. reflexivity.
        -- intros. reflexivity.
    - split.
        -- intros. pose proof Odd_or_Even. destruct H1 with k.
            + apply IHk in H2. specialize (H k). apply H in H2. 
            rewrite H0 in H2. discriminate H2.
            + specialize (H1 k) as H3. destruct H3.
                ++ apply IHk in H3. apply H in H3. rewrite H3 in H0. 
                discriminate H0.
                ++ destruct H2. Search (_ = _ -> S _ = S _).
                apply eq_S with (y := (2 * x + 1)) in H2. unfold Even.
                simpl in H2. exists (x + 1). simpl. 
                rewrite Nat.add_0_r in H2. rewrite Nat.add_1_r in H2.
                rewrite Nat.add_0_r. rewrite Nat.add_1_r.
                rewrite Nat.add_succ_r. rewrite Nat.add_comm.
                rewrite Nat.add_succ_r. apply H2.
        -- intro. pose proof Odd_or_Even. specialize (H1 k). destruct H1.
            + pose proof And_intro. specialize (H2 (Even k) (Even (S k))).
            apply H2 in H0. 
                ++ pose proof exclude_Even_succ. specialize (H3 k).
                apply H3 in H0. destruct H0. 
                ++ apply H1.
            + apply H. apply bi_contra_position in IHk.
            rewrite <- Odd_eq_not_Even in IHk. rewrite not_even_then_odd in IHk.
            rewrite even_eq_not_odd. rewrite notb_arg. simpl. apply IHk. apply H1.
Qed.

Lemma linear_comb_divisibility:
    ∀ a b d x y: nat, (d ∣ a) /\ (d ∣ b) -> (d ∣ (a * x + b * y)).
Proof.
    intros. destruct H. unfold divides in *. destruct H. destruct H0.
    exists (x0 * x + x1 * y). Search (_ * (_ + _)).
    rewrite Nat.mul_add_distr_l. Search (_ * (_ * _) = (_ * _) * _).
    rewrite Nat.mul_assoc. rewrite Nat.mul_assoc.
    rewrite H. rewrite H0.
    reflexivity.
Qed.

Lemma limitation: 
    ∀ d a : nat, (d ∣ a) -> a = 0 \/ d <= a.
Proof.
    intros. generalize dependent d. induction a.
    - intros. left; reflexivity.
    - intros. unfold divides in H. destruct H. destruct x.
        -- rewrite Nat.mul_0_r in H. discriminate H.
        -- right. rewrite Nat.mul_comm in H.
        simpl in H. rewrite H.
        Search (_ <= _ + _).
        apply Nat.le_add_r.
Qed.

Lemma divisibility_transitivity:
    ∀ a b c : nat, (a ∣ b) /\ (b ∣ c) -> a ∣ c.
Proof.
    intros. destruct H. unfold divides in *. destruct H. destruct H0.
    exists (x * x0). rewrite Nat.mul_assoc. rewrite <- H. rewrite <- H0.
    reflexivity.
Qed.

Lemma exist_quocient_and_rest:
    ∀ a b : nat, ∃ q r : nat, a = b * q + r.
Proof.
    intros. generalize dependent b. induction a.
    - intros. exists 0. exists 0. rewrite Nat.mul_0_r. simpl.
    reflexivity.
    - intros. specialize (IHa b). destruct IHa. destruct H. rewrite H.
    exists x. exists (S x0). rewrite Nat.add_succ_r. reflexivity.
Qed.

Definition quocient_and_rest (a b : nat) :=
    ∃ q r : nat, a = b * q + r /\ r < b.

(* Para provar o teorema de Euclides será necessário fazer um
Fixpoint que gere uma lista (conjunto) dos divisores de um natural
para seguir a ideia da prova exposta no livro de Martinez et al. *)

Fixpoint divisorsSetAux (a b : nat) : list nat:=
    match ((a/b) * b =? a) with
    | false => match b with
                | 0 => nil
                | S n => divisorsSetAux a n
                end
    | true => match b with
                | 0 => cons b nil
                | S n => S n :: (divisorsSetAux a n)
                end
    end.

Definition divisorsSet (a : nat) : list nat :=
    divisorsSetAux a a.

Require Import Coq.Lists.List.

Fixpoint intersectionSet (a b : list nat) : list nat :=
    match a with
    | nil => nil
    | cons h t => filter (fun x => if (x =? h) then true else false) b ++ intersectionSet t b
    end.

Notation "a ∩ b" := (intersectionSet a b) (at level 90, left associativity).

Lemma eqb_eq:
    ∀ n m : nat, n =? m = true <-> n = m.
Proof.
    intros. split.
    - intros. generalize dependent m. induction n.
        -- intros. destruct m.
            + reflexivity.
            + simpl in H; discriminate H.
        -- intros. destruct m.
            + simpl in H; discriminate H.
            + specialize (IHn m). f_equal. apply IHn. simpl in H. apply H.
    - intros. generalize dependent m. induction n.
        -- intros. destruct m.
            + simpl; reflexivity.
            + discriminate H.
        -- intros. rewrite <- H. simpl. specialize (IHn n). apply IHn.
        reflexivity. 
Qed.

Lemma intersectionSet_nil:
    ∀ A : list nat, intersectionSet A nil = nil.
Proof.
    intros. induction A as [|h t].
    - simpl. reflexivity.
    - simpl. apply IHt.
Qed.

Compute intersectionSet (1 :: (2 :: (1 :: nil))) (1 :: (1 :: (2 :: nil))).
Compute intersectionSet (1 :: (1 :: (2 :: nil))) (1 :: (2 :: (1 :: nil))).

Lemma in_app_eq_or:
    ∀ n : nat, ∀ a b : list nat, In n (a ++ b) <-> In n a \/ In n b.
Proof.
    intros. split.
    - intros. induction a as [|h t].
        -- simpl in H. right; apply H.
        -- simpl. simpl in H. destruct H.
            + left. left. apply H.
            + apply IHt in H. destruct H.
                ++ left; right. apply H.
                ++ right. apply H.
    - intros. induction a as [|h t].
        -- simpl. destruct H.
            + destruct H.
            + apply H.
        -- simpl. simpl in H. destruct H.
            + destruct H.
                ++ left. apply H.
                ++ right. apply IHt. left. apply H.
            + right. apply IHt. right. apply H.
Qed.

Theorem intersectionSet_comm: 
    ∀ A B : list nat, ∀ n : nat, In n (A ∩ B) <-> In n (B ∩ A).
Proof.
    intro A. induction A.
    - intros. simpl. rewrite intersectionSet_nil. reflexivity.
    - intros. induction B.
        -- simpl. rewrite intersectionSet_nil. simpl. reflexivity.
        -- simpl. destruct (a0 =? a) eqn:Case.
            + Search (_ =? _). rewrite Nat.eqb_sym in Case.
            rewrite Case. simpl.
            Search (In). rewrite in_app_eq_or. rewrite in_app_eq_or.
            rewrite <- IHB. specialize (IHA (a0 :: B)) as IHA0. simpl. rewrite in_app_eq_or.
            rewrite IHA0. simpl. rewrite in_app_eq_or. rewrite IHA.
            apply eqb_eq in Case. rewrite Case. 
            assert (∀ X Y Z T : Prop, X \/ Y \/ Z \/ T <-> X \/ Z \/ Y \/ T ).
            {
                intros. rewrite <- or_assoc. rewrite <- or_assoc.
                rewrite -> or_assoc with (A := X). rewrite or_comm with (A := Y).
                rewrite <- or_assoc. rewrite or_assoc. rewrite or_assoc. reflexivity.
            }
            apply H.
            + rewrite Nat.eqb_sym in Case. rewrite Case. rewrite in_app_eq_or.
            rewrite in_app_eq_or. rewrite <- IHB. rewrite IHA. simpl. rewrite in_app_eq_or.
            rewrite in_app_eq_or. rewrite IHA. rewrite <- or_assoc. rewrite or_comm with (A := In n (filter (λ x : nat, if x =? a then true else false) B)).
            rewrite or_assoc. reflexivity.
Qed.

Lemma in_filter:
    ∀ n : nat, ∀ A : list nat, In n A <-> In n (filter (fun x => if (x =? n) then true else false) A).
Proof.
    intros. split. intros. induction A as [|h t].
    - destruct H.
    - simpl in H. destruct H.
        -- simpl. rewrite H. Search (_ =? _). pose proof Nat.eqb_refl. specialize (H0 n).
        rewrite H0. simpl. left. reflexivity.
        -- simpl. destruct (h =? n) eqn:Case.
            + simpl. rewrite eqb_eq in Case. left. apply Case.
            + apply IHt. apply H.
    - intros. induction A as [|h t].
        -- simpl in H. destruct H.
        -- simpl. simpl in H. destruct (h =? n) eqn:Case.
            + left. apply eqb_eq in Case. apply Case.
            + right. apply IHt. apply H.
Qed.

Lemma in_filter_element: 
    ∀ m n : nat, ∀ A : list nat, In n (filter (fun x => if (x =? m) then true else false) A) <-> In m A /\ m = n.
Proof.
    intros. split.
    - intros. induction A as [|h t].
        -- destruct H.
        -- simpl in H. destruct (h =? m) eqn:Case.
            + simpl in H. destruct H.
                ++ simpl. rewrite eqb_eq in Case. split.
                    * left. apply Case.
                    * rewrite Case in H. apply H.
                ++ apply IHt in H. destruct H. rewrite eqb_eq in Case. split.
                    * simpl. right. apply H.
                    * apply H0.
            + apply IHt in H. destruct H. simpl. split.
                ++ right. apply H.
                ++ apply H0.
    - intros. destruct H. induction A as [|h t].
        -- destruct H.
        -- simpl. destruct (h =? m) eqn:Case.
            + simpl in H. simpl. rewrite eqb_eq in Case. left. rewrite Case. apply H0.
            + simpl in H. apply IHt. destruct H.
                ++ apply eqb_eq in H. rewrite Case in H. discriminate H.
                ++ apply H.
Qed.

Theorem intersectionSet_correctness: 
    ∀ n : nat, ∀ A B : list nat, In n A /\ In n B <-> In n (A ∩ B).
Proof.
    intros. split.
    - generalize dependent A. induction B.
        -- intros. simpl in H. destruct H. destruct H0.
        -- intros. destruct H. rewrite intersectionSet_comm. simpl.
        rewrite in_app_eq_or. destruct A.
            + destruct H.
            + simpl in H0. destruct H0.
                ++ left. rewrite H0. apply -> in_filter. apply H.
                ++ right. rewrite intersectionSet_comm. apply IHB. split.
                    * apply H.
                    * apply H0.
    - generalize dependent B. induction A.
        -- intros. destruct H.
        -- intros. simpl in H. rewrite in_app_eq_or in H. destruct H.
            + apply in_filter_element in H. destruct H. split.
                ++ simpl. left. apply H0.
                ++ rewrite <- H0. apply H.
            + apply IHA in H. destruct H. simpl. split.
                ++ right. apply H.
                ++ apply H0.
Qed.

Definition get_max (A : list nat) : nat :=
    fold_left (fun n m => if (m <=? n) then n else m) A 0.
    
Lemma aux_get_max:
    ∀ n : nat, ∀ A : list nat, n <= fold_left (fun n m => if (m <=? n) then n else m) A n.
Proof.
    intros. generalize dependent n. induction A as [|h t].
    - intros. simpl. apply le_n.
    - intros. simpl. destruct (h <=? n) eqn:Case.
        -- apply IHt.
        -- specialize (IHt h). Search (_ <=? _). apply Nat.leb_gt in Case.
        Search (_ < _). apply Nat.lt_le_incl in Case. transitivity h.
            + apply Case.
            + apply IHt.
Qed.

(* Lemma extensionality:
    ∀ t : list nat,
    (fix get_max (A : list nat) : nat :=
    fold_left (λ n0 m : nat, if m <=? n0 then n0 else m) A 0) t 
    = 
    fold_left (λ n0 m : nat, if m <=? n0 then n0 else m) t 0.
Proof.
    intros. destruct t.
    - simpl. reflexivity.
    - simpl. reflexivity.  
Abort. *)

Lemma get_max_aux2:
    ∀ h, ∀ t, 
    h <= fold_left (λ n0 m : nat, if m <=? n0 then n0 else m) t h.
Proof.
    intros. generalize dependent h. induction t as [|x xs].
    - intros. simpl. apply le_n.
    - simpl. intros. destruct (x <=? h) eqn:Case1.
        + apply IHxs.
        + specialize (IHxs x). transitivity x.
            ++ apply Nat.leb_gt in Case1. apply Nat.lt_le_incl in Case1.
            apply Case1.
            ++ apply IHxs.
Qed.
(* 
Lemma get_max_aux3:
    ∀ h1 h2, ∀ t, 
    (h1 <=? h2) = true -> get_max (h1 :: t) <= get_max (h2 :: t).
Proof.
    intros. generalize dependent h1. generalize dependent h2.
    induction t as [|x xs].
    - intros. destruct (h1 <=? 0) eqn:Case1.
        { unfold get_max. simpl. rewrite Case1. apply Nat.le_0_l. }
        { unfold get_max. simpl. rewrite Case1.  }
        --
        
         apply leb_complete in H. transitivity h2.
            + simpl. rewrite Case1. apply H.
            + simpl. destruct (h2 <=? 0) eqn:Case2.
                ++ rewrite Nat.leb_le in Case2. apply Case2.
                ++ apply le_n.
    - intros. destruct (h2 <=? 0) eqn:Case1. apply leb_complete in Case1 as H1.
    apply Nat.le_0_r in H1. rewrite H1 in H.
        -- simpl. rewrite H. rewrite H1. simpl. apply le_n.
        -- destruct (h1 <=? 0) eqn:Case2.
            + simpl. rewrite Case1. rewrite Case2. destruct (x <=? h2) eqn:Case3.
                ++ destruct (x <=? 0) eqn:Case4.
                    * specialize (IHxs h2 0). simpl in IHxs. rewrite Case1 in IHxs.
                    apply IHxs. reflexivity.
                    * specialize (IHxs h2 x). simpl in IHxs. rewrite Case4 in IHxs.
                    rewrite Case1 in IHxs. apply IHxs. apply Case3.
                ++ destruct (x <=? 0) eqn:Case4.
                    * apply leb_complete in Case4. rewrite Nat.le_0_r in Case4.
                    rewrite Case4. apply le_n.
                    * apply le_n.
            + simpl. rewrite Case1. rewrite Case2. destruct (x <=? h1) eqn:Case3.
                ++ destruct (x <=? h2) eqn:Case4.
                    * specialize (IHxs h2 h1). simpl in IHxs. rewrite Case1 in IHxs.
                    rewrite Case2 in IHxs. apply IHxs. apply H.
                    * apply leb_complete_conv in Case4. apply leb_complete in Case3.
                    apply leb_complete in H. assert (x <= h2).
                    {
                        transitivity h1. apply Case3. apply H.   
                    }
                    apply lt_not_le in Case4. apply Case4 in H0. destruct H0.
                ++ destruct (x <=? h2) eqn:Case4.
                    * specialize (IHxs h2 x). simpl in IHxs.
                    rewrite Case1 in IHxs. assert ((x <=? 0) = false).
                    {
                        rewrite leb_iff_conv in Case3. rewrite leb_iff_conv in Case2.
                        rewrite leb_iff_conv. transitivity h1.
                        apply Case2. apply Case3.
                    }
                    rewrite H0 in IHxs. apply IHxs. 
                    apply Case4.
                    * apply le_n.
Qed.           *)

(* Lemma get_max_aux4:
    ∀ h, ∀ t, 
    get_max t <= get_max (h :: t).
Proof.
    intros. generalize dependent h.
    induction t as [|x xs].
    - intros. simpl. apply Nat.le_0_l.
            }
    - intros. simpl (get_max (h :: x :: xs)). destruct (h <=? 0) eqn:Case1.
        -- simpl. apply le_n.
        -- destruct (x <=? h) eqn:Case2.
            + pose proof get_max_aux3. specialize (H x h xs). simpl in H.
            rewrite Case1 in H. simpl. apply H. apply Case2.
            + simpl. assert ((x <=? 0) = false).
            {
                rewrite leb_iff_conv. rewrite leb_iff_conv in Case1.
                transitivity h.
                    ++ apply Case1.
                    ++ rewrite leb_iff_conv in Case2. apply Case2.   
            rewrite H. apply le_n.
Qed. *)
(* 
Lemma get_max_correctness: 
    ∀ A : list nat, ∀ n : nat, In n A -> n <= (get_max A).
Proof.
    intros. generalize dependent n. induction A as [|h t].
    - intros. destruct H.
    - intros. simpl in H. destruct H.
        -- simpl. destruct (h <=? 0) eqn:Case.
            + Search (_ <=? _). apply leb_complete in Case.
            Search (_ <= _). apply le_n_0_eq in Case as H1.
            rewrite H1. Search (_ <= _). rewrite <- H1. rewrite <- H. 
            rewrite <- H1. apply Nat.le_0_l.
            + rewrite H. apply aux_get_max.
        -- destruct (h <=? 0) eqn:Case.
            + unfold get_max. simpl. rewrite Case. unfold get_max in IHt.
            destruct t.
            (* Foi necessário o destruct por causa do "fix" que não pode ser
            reduzido sem uma iteração *)
                ++ destruct H.
                ++ apply IHt. apply H.
            + simpl. rewrite Case. destruct (n <=? h) eqn:Case1.
                ++ Search (_ <=? _). apply leb_complete in Case1.
                transitivity h.
                    * apply Case1.
                    * apply aux_get_max.
                ++ apply IHt in H. pose proof get_max_aux4. specialize (H0 h t).
                simpl in H0. rewrite Case in H0. transitivity (get_max t).
                    * apply H.
                    * apply H0.
Qed. *)

Definition gcd (a b n : nat) := 
    ((n ∣ a) /\ (n ∣ b)) /\ (∀ m : nat, (m ∣ a) /\ (m ∣ b) -> m <= n).

Lemma divides_zero:
    ∀ n : nat, n ∣ 0.
Proof.
    intros. unfold divides. exists 0. rewrite Nat.mul_0_r. reflexivity.
Qed.

Lemma divides_itself:
    ∀ n : nat, n ∣ n.
Proof.
    intros. unfold divides. exists 1. rewrite Nat.mul_comm. simpl.
    rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma gcd_max_aux1:
    ∀ n : nat, divisorsSetAux (S n) (S n) = (S n) :: divisorsSetAux (S n) n.
Proof.
    intros. unfold divisorsSetAux. assert ((S n / S n * S n =? S n) = true).
    {
     intros. Search (_/_).  Search (S _ ≠ 0). pose proof Nat.neq_succ_0.
     specialize (H n). apply Nat.div_same in H. rewrite H. simpl. rewrite Nat.add_0_r.
     Search (_ =? _). apply Nat.eqb_refl.
    }
    rewrite H. reflexivity.
Qed. 

Lemma gcd_max_aux2:
    ∀ n h : nat, ∀ t : list nat, divisorsSet n = h :: t -> (h ∣ n).
Proof.
    intros. unfold divisorsSet in *. generalize dependent h.
    generalize dependent t. induction n.
    - intros. apply divides_zero.
    - intros. rewrite gcd_max_aux1 in H. inversion H. unfold divides.
    exists 1. rewrite Nat.mul_comm. simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

Compute (1/0).

Lemma gcd_max_aux3:
    ∀ n : nat, ~ (In 0 (divisorsSet n)).
Proof.

Admitted.

Lemma gcd_max_aux4:
    ∀ m n : nat, In m (divisorsSet n) -> m ∣ n.
Proof.
    intros. generalize dependent n. induction m as [|k]. 
    - intros. apply gcd_max_aux3 in H. destruct H.
    - intros.
Abort.

Theorem gcd_max: 
    ∀ a b : nat, gcd a b (get_max (intersectionSet (divisorsSet a) (divisorsSet b))).
Proof.
    intros. unfold gcd. split.
    - split.
        -- induction a as [|k].
            + apply divides_zero.
            +  
Abort.

Lemma divisible_mult:
    ∀ a n : nat, (n ∣ a) -> ∀ a0 : nat, (n ∣ (a0 * a)).
Proof.
    intros. unfold divides in *. destruct H. exists (a0 * x).
    rewrite Nat.mul_assoc. symmetry.
    rewrite <- Nat.mul_assoc. rewrite Nat.mul_comm. 
    rewrite <- Nat.mul_comm in H. rewrite H.
    rewrite Nat.mul_assoc. reflexivity.
Qed.

Lemma divisible_diff:
    ∀ a b : nat, ∀ n : nat, (n ∣ a) /\ (n ∣ b) -> (n ∣ (a - b)).
Proof.
    intros. unfold divides in *. destruct H. destruct H.
    destruct H0. exists (x - x0). Search (_ * (_ - _)).
    rewrite Nat.mul_sub_distr_l. rewrite H. rewrite H0.
    reflexivity.
Qed.

Theorem Euclides:
    ∀ a b q r n : nat, a = b * q + r -> 
    r < b ->
    gcd a b n -> 
    gcd b r n.
Proof. 
    unfold gcd in *.  intros. destruct H1. destruct H1. split. 
    - split.
        -- apply H3.
        -- Search (_ - _ = _). symmetry in H.
        apply Nat.add_sub_eq_r in H as H4. rewrite <- H in H1.
        pose proof divisible_mult. specialize (H5 b n).
        apply H5 with (a0 := q) in H3. rewrite Nat.mul_comm in H3.
        rewrite Nat.add_comm in H1. pose proof divisible_diff.
            + specialize (H6 (r + b * q) (b * q) n). Search (_ + _ - _).
            rewrite Nat.add_sub in H6. apply H6. split.
                ++ apply H1.
                ++ apply H3.
    - intros. apply H2. destruct H4. split.
        -- pose proof linear_comb_divisibility. specialize (H6 b r m q 1).
        rewrite Nat.mul_1_r in H6. rewrite H. apply H6. split.
            + apply H4.
            + apply H5.
        -- apply H4.
Qed.

Search (leb).

Fixpoint Div (a b : nat) : nat :=
    match b <=? a with
    | true => match a, b with
             | S n, S m => S (Div (n - m) b)
             | _ , _ => 0
             end
    | false => 0
    end.

Fixpoint Mod (a b : nat) : nat :=
    match b <=? a with
    | true => match a, b with
            | S n, S m => Mod (n - m) b
            | S n, 0 => S n
            | _ , _ => 0
            end
    | false => a
    end.

Notation "a / b" := (Div a b).

Lemma div_zero:
    ∀ n : nat, Div n 0 = 0.
Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Lemma div_dist:
    ∀ m n p: nat, Div (n + m) p = (Div n p) + (Div m p).
Proof.
    intro. induction m.
    - intros. simpl. rewrite Nat.add_0_r. destruct p.
        -- simpl. rewrite div_zero. simpl. reflexivity.
        -- simpl. rewrite Nat.add_0_r. reflexivity.
    - intros. simpl. destruct (p <=? S m) eqn:Case.
        -- destruct p.
            + rewrite div_zero. rewrite div_zero. reflexivity.
            + specialize (IHm (S n) (S p)) as H0. simpl ((S n) + m) in H0.
            rewrite plus_n_Sm in H0. rewrite H0. simpl.
Abort. 

Lemma added_both_sides:
    ∀ a b n, a + n = b + n <-> a = b.
Proof.
    intros. split.
    - intros. induction n.
        -- repeat rewrite Nat.add_0_r in H. apply H.
        -- apply IHn. repeat rewrite Nat.add_succ_r in H.
        injection H. intros. apply H0.
    - intros. rewrite H. reflexivity.
Qed.

Lemma mult_both_sides:
    ∀ a b n, n <> 0 -> a * n = b * n <-> a = b.
Proof.
    intros. split.
    - generalize dependent n. generalize dependent b. 
    induction a.
        -- intros. simpl in H0. destruct n.
            + exfalso. apply H. reflexivity.
            + destruct b.
                ++ reflexivity.
                ++ simpl in H0. discriminate H0.
        -- intros. simpl in H0. rewrite <- Nat.add_1_r.
        generalize dependent n. induction b.
            + intros. simpl in H0. destruct n.
                ++ destruct H. reflexivity.
                ++ simpl in H0. discriminate H0.
            + intros. rewrite Nat.add_1_r.
            apply f_equal. simpl in H0. 
            rewrite Nat.add_comm in H0.
            symmetry in H0.
            rewrite Nat.add_comm in H0.
            symmetry in H0.
            rewrite (added_both_sides (a * n) (b * n) n) in H0.
            apply IHa with (n := n).
                ++ apply H.
                ++ apply H0.
    - intros. rewrite H0. reflexivity.
Qed.

Lemma div_per_one:
    ∀ n, Div n 1 = n.
Proof.
    intros. induction n.
    - reflexivity.
    - simpl. destruct n.
        -- simpl. reflexivity.
        -- simpl in IHn. simpl. rewrite IHn. reflexivity.
Qed.

Lemma it_self_frac:
    ∀ n m : nat, (m <> 0) /\ (m ∣ n) -> m * (Div n m) = n.
Proof.
    intros. generalize dependent m. induction n as [|k].
    - intros. simpl. destruct H. destruct m.
        -- destruct H. reflexivity.
        -- simpl. rewrite Nat.mul_comm. reflexivity.
    - intros. destruct H. simpl. 
    pose proof (limitation m (S k)). apply H1 in H0 as H2.
    destruct H2.
        -- discriminate H2.
        -- apply Nat.leb_le in H2. rewrite H2.
        destruct m.
            + destruct H. reflexivity.
            + rewrite Nat.mul_succ_r. specialize (IHk (S m)).
            rewrite Nat.leb_le in H2. Search (_ /\ _).
            pose proof (conj H H0).
Abort. 
    
Lemma remainder_to_one:
    ∀ n, Mod n 1 = 0.
Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite Nat.sub_0_r. apply IHn.
Qed.

Lemma succ_leq_one:
    ∀ n, 1 < S n \/ 1 = S n.
Proof.
    intros. induction n.
    - right. reflexivity.
    - left. destruct IHn.
        -- transitivity (S n).
            + apply H.
            + unfold lt. apply le_n.
        -- unfold lt. rewrite H. apply le_n.
Qed.

Lemma div_greater_eq_0:
    ∀ m n, m < n -> Div m n = 0.
Proof.
    induction m.
    - intros. simpl. destruct n.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
    - intros. simpl. Search (_ < _). apply Nat.lt_nge in H.
    Search (_ <= _). apply Nat.leb_nle in H. rewrite H.
    reflexivity.
Qed.

Lemma div_suc_arg:
    ∀ a b, b <> 0 /\ b <= a -> Div a b = S (Div (a - b) b).
Proof.
    intros. generalize dependent b.
    induction a.
    - intros. destruct H. destruct H. inversion H0.
    reflexivity.
    - intros. destruct H. simpl. rewrite <- Nat.leb_le in H0.
    rewrite H0. destruct b.
        + destruct H. reflexivity.
        + reflexivity.
Qed.

(* Propriedades de módulo *)

Lemma remainder_to_zero:
    ∀ n, Mod n 0 = n.
Proof.
    induction n.
    - reflexivity.
    - simpl. reflexivity.
Qed.

Compute (1 mod 2).
Search (_ mod _).


Lemma Mod_transitivity: 
    ∀ a b n, Mod a n = Mod b n -> ∀ k, Mod (a + k) n = Mod (b + k) n.
Proof.
    intros. generalize dependent a.
    generalize dependent b. induction k.
    - i 
             
Qed.


Lemma correctness_Mod: 
    ∀ a b q r: nat, a = b * q + r /\ 0 <= r /\ r < b -> r = Mod a b.
Proof.
    induction a.
    - intros. simpl. induction b.
        -- simpl. destruct H. destruct H0. inversion H1.
        -- simpl. destruct H. destruct r.
            + reflexivity.
            + rewrite Nat.add_succ_r in H. discriminate H.
    - intros. destruct H. destruct H0. simpl. 
            

Lemma correctness_Mod: 
    ∀ a b : nat, b <> 0 -> (a = b * (Div a b) + (Mod a b) /\ (Mod a b) < b).
Proof.
    intros. generalize dependent b.
    - induction a.
        -- split.
            + simpl. destruct b.
                ++ simpl. reflexivity.
                ++ simpl. rewrite Nat.mul_0_r.
                reflexivity.
            + simpl. induction b.
                ++ destruct H. reflexivity.
                ++ simpl. apply Nat.lt_0_succ.
        -- intros. split.
            + simpl. destruct (b <=? S a) eqn:Case1.
                ++ destruct b.
                    * destruct H. reflexivity.
                    * apply IHa in H. simpl in H.
                    destruct H. simpl. apply f_equal. 


                
Qed.


Fixpoint EuclidesAlgorithm (a b : nat) : nat :=
    match b with
    | 0 => a
    | S n => match a with
            | 0 => b
            | S m => EuclidesAlgorithm b (n - snd (Nat.divmod a n 0 n))
            end
    end.

Compute EuclidesAlgorithm 8 6.

Print Nat.divmod.

Theorem EuclidesAlgorithm_correctness: 
    ∀ a b n : nat, EuclidesAlgorithm a b = n <-> gcd a b n.
Proof.
    intros. split.
    - intros. unfold gcd. split.
        -- generalize dependent b. generalize dependent n. induction a as [|k].
            + intros. unfold EuclidesAlgorithm in H. destruct b.
                ++ split.
                    * apply divides_zero.
                    * apply divides_zero.
                ++ split.
                    * apply divides_zero.
                    * rewrite H. apply divides_itself.
            + split.
                ++ destruct b eqn:Case1.
                    * simpl in *. rewrite H. apply divides_itself.
                    * simpl in H.
Qed.