(* Primeira Prova de Métodos Formais 16/10/2023
   Nome: Bruno Rafael dos Santos               *)

(* Todas as declarações devem ser feitas nesse arquivo,
   não deve ser importado nenhum módulo. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* Questão 1 - Prove o teorema true_or. *)

Lemma or_comm : forall (b1 b2 : bool), b1 || b2 = b2 || b1.
Proof.
  intros. destruct b1 eqn:Case1.
  - destruct b2 eqn:Case2.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
  - destruct b2 eqn:Case2.
    -- reflexivity.
    -- reflexivity.
Qed. 

Theorem true_or : forall (b1 b2:bool), b1 = true \/ b2 = true -> b1 || b2 = true.
Proof.
  intros. destruct H.
  - rewrite H. simpl. reflexivity.
  - rewrite H. rewrite or_comm. simpl. reflexivity.
Qed.  

(* Questão 2 - Prove que a função fold_map é equivalente a função map (fold_map_correct). *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x l' => f x :: l') l [].
  
Theorem fold_map_correct : forall (X Y: Type) (f: X -> Y) (l: list X),
  map f l = fold_map f l.
Proof.
  intros. induction l as [|h t].
  - simpl. unfold fold_map. simpl. reflexivity.
  - simpl. unfold fold_map in *. simpl. rewrite IHt. reflexivity.
Qed.

(* Questão 3 - Prove o teorema involutive_f_map *)

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation "g (.) f" := (compose g f)
                     (at level 5, left associativity).

Theorem involutive_f_map : forall (A : Type)(f : A -> A) (l:list A), 
  (forall x:A, f (f x) = x) -> map f (.) f l = l.
Proof.
  intros. induction l as [|h t].
  - simpl. reflexivity.
  - simpl. specialize (H h). unfold compose in *. rewrite H. rewrite IHt. reflexivity.
Qed.

(* Questão 4 - Prove a propriedade distributiva do \/ sobre o /\ (or_distributes_over_and). *) 

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ]. 
  - right. apply HP.
  - left. apply HQ.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros. destruct H. split.
  - left. apply H.
  - left. apply H.
  - destruct H. split.
    -- right. apply H.
    -- right. apply H0.
Qed.