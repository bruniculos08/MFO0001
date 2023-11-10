(* Aluno: Bruno Rafael dos Santos *)

Require Export Coq.Lists.List.
Import ListNotations.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros. destruct H0. apply H0.
  specialize (H x). apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H. destruct H.
    -- left. exists x. apply H.
    -- right. exists x. apply H.
  - intros. destruct H.
    -- destruct H. exists x. left. apply H.
    -- destruct H. exists x. right. apply H.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros. destruct H. destruct H. split.
  - exists x. apply H.
  - exists x. apply H0.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros. generalize dependent x. induction l as [|h t].
  - intros. simpl in H. destruct H.
  - intros. simpl. simpl in H. destruct H.
    -- left. apply f_equal. apply H.
    -- right. apply IHt in H. apply H.
Qed. 

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - intro. generalize dependent y. 
  induction l as [|h t].
    -- intros. simpl in H. destruct H.
    -- intros. simpl in H. destruct H.
      --- exists h. simpl. split.
        ---- apply H.
        ---- left. reflexivity.
      --- apply IHt in H. destruct H. destruct H. exists x. split.
        ---- apply H.
        ---- simpl. right. apply H0.
  - generalize dependent y. intros. destruct H. destruct H.
  induction l as [|h t].
    -- simpl in H0. destruct H0.
    -- simpl in H0. destruct H0.
      --- simpl. left. rewrite <- H0 in H. apply H.
      --- simpl. right. apply IHt. apply H0.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros. split.
    -- intros. simpl in H. right. apply H.
    -- intros. simpl. destruct H.
      --- simpl in H. destruct H.
      --- apply H.
  - intros. split.
    -- intros. simpl in H. simpl. destruct H.
      --- left. left. apply H.
      --- apply IH in H. destruct H.
        ---- left. right. apply H.
        ---- right. apply H.
    -- intros. destruct H.
      --- simpl in H. simpl. destruct H.
        ---- left. apply H.
        ---- right. apply IH. left. apply H.
      --- simpl. right. apply IH. right. apply H.
Qed.  

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros. unfold not. intros. apply H. right. 
  intros. apply H. left. apply H0.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros. destruct H.
  - apply H in H0. destruct H0.
  - apply H.
Qed.

Theorem Peirce_double_negation: forall (P:Prop), (forall P Q: Prop,
  (((P->Q)->P)->P)) -> (~~ P -> P).
Proof.
  intros. apply H with (Q := ~P). intros. apply H with (Q := P).
  apply disj_impl. left. unfold not. intros. unfold not in H0. 
  apply H0. intros. apply H1 in H3 as H4. apply H4 in H3. apply H3.
Qed.

Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (P:Prop), (~~ P -> P)) -> (P \/ ~P). 
Proof.
  intros. apply H. unfold not. intros. apply H0. right. intro.
  apply H0. left. apply H1.
Qed.


   








