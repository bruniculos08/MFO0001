(* Exercícios - Expressões Regulares *)
(* Aluno: Bruno Rafael dos Santos *)

Require Export Coq.Init.Logic.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Import ListNotations.


Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.


(* Exercício 1*)
(* Dica pode ser necessário o uso da tática [generalize dependent]. *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros. split.
  - intros. generalize dependent s1. induction s2.
    -- intros. simpl in H. inversion H. reflexivity.
    -- intros. simpl in H. inversion H. apply IHs2 in H4.
    rewrite H4. inversion H3. reflexivity.
  - intros. generalize dependent s1. induction s2.
    -- intros. simpl. rewrite H. apply MEmpty.
    -- intros. rewrite H. simpl. assert (a :: s2 = [a] ++ s2).
    {
     simpl. reflexivity. 
    }
    rewrite H0. apply MApp.
      --- apply MChar.
      --- apply IHs2. reflexivity.
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
end.

(* Exercício 2*)
Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros. split.
  - intros. destruct H. induction H.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
    -- simpl. rewrite IHexp_match1. rewrite IHexp_match2.
    simpl. reflexivity.
    -- simpl. rewrite IHexp_match. simpl. reflexivity.
    -- simpl. rewrite IHexp_match. Search (_||true). 
    rewrite orb_true_r. reflexivity.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
  - intros. induction re.
    -- simpl in H. discriminate H.
    -- exists []. apply MEmpty.
    -- exists [t]. apply MChar.
    -- simpl in H. Search (_ && _ = true). apply andb_true_iff in H. destruct H.
    apply IHre1 in H. apply IHre2 in H0. destruct H. destruct H0. exists (x ++ x0).
    apply MApp.
      --- apply H.
      --- apply H0.
    -- simpl in H. apply orb_true_iff in H. destruct H.
      --- apply IHre1 in H. destruct H. exists x. apply MUnionL. apply H.
      --- apply IHre2 in H. destruct H. exists x. apply MUnionR. apply H.
    -- exists []. apply MStar0.
Qed.

(* Exercício 3*)

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma succ_le_then: forall x y : nat,
  x <= y -> S x <= S y.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed. 

Lemma sum_le : forall x y z : nat,
  x + y <= z -> x <= z /\ y <= z.
Proof.
  intros. induction H.
  - split.
    -- induction x.
      --- destruct y.  
          ---- simpl. apply le_n.
          ---- simpl. apply le_S. Search(0 <= _). apply PeanoNat.Nat.le_0_l.
      --- simpl. apply succ_le_then in IHx. apply IHx.
    -- induction y.
      --- simpl. apply PeanoNat.Nat.le_0_l.
      --- simpl. rewrite PeanoNat.Nat.add_succ_r. 
        apply succ_le_then. apply IHy.
  - split.
    -- destruct IHle. apply le_S. apply H0.
    -- destruct IHle. apply le_S. apply H1.
Qed.

Lemma napp_nil : forall T : Type, forall n : nat,
  @napp T n [] = [].
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.

Lemma  napp_plus: forall T : Type, forall m n : nat, forall s : list T,
  napp (n + m) s = napp n s ++ napp m s.
Proof.
  intros.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn. rewrite app_assoc. reflexivity.
Qed.

(* Lemma star_empty : forall T : Type, forall s : list T,
  s =~ Star EmptyStr -> s = [].
Proof.
  intros.
 *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** Complete the proof below. Several of the lemmas about [le] that
    were in an optional exercise earlier in this chapter may also be
    useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - intros. simpl in H. inversion H. inversion H1.
  - intros. simpl in H. Search (length (_ ++ _)). rewrite app_length in H.
  Search (_ + _ <= _ + _). apply PeanoNat.Nat.add_le_cases in H. destruct H.
    -- apply IH1 in H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    exists x. exists x0. exists (x1 ++ s2). split.
      --- rewrite H. Search(_ ++ _). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      --- split.
        + apply H0.
        + intros. rewrite app_assoc. rewrite app_assoc. apply MApp.
          ++ rewrite <- app_assoc. apply H1.
          ++ apply Hmatch2.
    -- apply IH2 in H. destruct H. destruct H. destruct H. destruct H. destruct H0. exists (s1 ++ x).
    exists x0. exists x1. split.
      --- rewrite <- app_assoc. rewrite H. reflexivity.
      --- split.
        + apply H0.
        + intros. rewrite <- app_assoc. 
        (* Lembrar-se aqui da associatividade à direita da função "++" *)
        apply MApp.
          ++ apply Hmatch1.
          ++ apply H1.
  - intros. simpl in H. apply sum_le in H. destruct H. apply IH in H.
  destruct H. destruct H. destruct H. destruct H. destruct H1. exists x.
  exists x0. exists x1. split.
    -- apply H.
    -- split.
      + apply H1.
      + intros. apply MUnionL. apply H2.
  - intros. simpl in H. apply sum_le in H. destruct H. apply IH in H0.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. exists x. 
  exists x0. exists x1. split.
    -- apply H0.
    -- split.
      + apply H1.
      + intros. apply MUnionR. apply H2.
  - intros. simpl in H. exists []. exists []. exists []. split.
    -- simpl. reflexivity.
    -- split.
      + induction re.
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
        ++ apply IHre1. simpl in H. apply sum_le in H. destruct H. apply H.
        ++ apply IHre1. simpl in H. apply sum_le in H. destruct H. apply H.
        ++ apply IHre. simpl in H. apply H.
      + intros. simpl. Search(_ ++ []). induction re.
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
        ++ simpl in H. apply sum_le in H. destruct H. apply IHre1 in H.
        apply IHre2 in H0. rewrite app_nil_r. rewrite napp_nil. apply MStar0.
        ++ simpl in H. apply sum_le in H. destruct H. apply IHre1 in H.
        apply IHre2 in H0. rewrite app_nil_r. rewrite napp_nil. apply MStar0.
        ++ rewrite app_nil_r. rewrite napp_nil. apply MStar0.
  - intros. simpl in H. rewrite app_length in H. destruct (length s1) eqn:Case.
    -- simpl in H. assert (s1 = []). {
      destruct s1. reflexivity. simpl in Case. discriminate Case.
    }
    rewrite H0. simpl. simpl in IH2. apply IH2 in H. apply H.
    -- exists [], s1, s2. simpl. split.
      --- reflexivity.
      --- split.
        ++ intro. rewrite H0 in Case. simpl in Case. discriminate Case.
        ++ intros. destruct s1.
          +++ discriminate Case.
          +++ induction m as [| k IHk].
            ++++ simpl. apply Hmatch2.
            ++++ assert(Hk : S k = plus 1 k).
            {
              reflexivity.
            }
            rewrite Hk.
            rewrite napp_plus.
            rewrite <- app_assoc.
            apply MStarApp.
            ---- simpl. rewrite app_nil_r. apply Hmatch1.
            ---- apply IHk.
  Qed.
        
(** [] *)