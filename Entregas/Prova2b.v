(* Exame Métodos Formais 
   Nome: Bruno Rafael dos Santos *)

(* Todas as declarações devem ser feitas nesse arquivo,
   não deve ser importado nenhum módulo adicional. *)

Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Questão 1 *)

Theorem repeat_n : forall {X:Set} (n:nat) (x:X),
  length (repeat x n) = n.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Questão 2 *)

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros. destruct H. destruct H. split.
  - exists x. apply H.
  - exists x. apply H0.
Qed.
  
(* Questão 3 *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction b.
  - simpl. Search(_+0). rewrite <- plus_n_O. apply le_n. 
  - rewrite <- plus_n_Sm. apply le_S. apply IHb.
Qed.

(* Questão 4 *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Lemma union_inv : forall T (s : list T) (r1 r2 : reg_exp),
   s =~ r1 \/ s =~ r2 <-> s =~ Union r1 r2.
Proof.
  intros. split.
  - intros. destruct H. 
    -- apply MUnionL. apply H.
    -- apply MUnionR. apply H.
  - intros. inversion H.
    -- left. apply H2.
    -- right. apply H1.
Qed.