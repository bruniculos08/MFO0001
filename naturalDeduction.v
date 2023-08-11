Module naturalDeduction.

Theorem neg_impli_right: forall(P Q: Prop),
    ~(P->Q) -> ~Q.
Proof.
    intros. contradict H. intro. apply H.    
Qed.

Theorem letterA2: forall A : Prop,
    ~A -> (A -> False).
Proof.
    intros. apply H in H0. apply H0.
Qed.

Theorem letterB2: forall A : Prop,
    ~(A /\ ~A).
Proof.
    intros. intro. destruct H. 
    apply H0 in H. apply H.
Qed.

Theorem letterC2: forall A B C : Prop,
    ((A->C) /\ (B->C)) -> ((A \/ B) -> C).
Proof.
    intros. destruct H0.
    - destruct H. apply H in H0. apply H0.
    - destruct H. apply H1 in H0. apply H0.
Qed.

Theorem letterA3: forall A : Prop,
    (~A)->(A->False).
Proof.
    intros. apply H in H0. apply H0.
Qed.

Theorem letterI3: forall A B : Prop,
    ((A->B)->A) -> A.
Proof.
    intros.  
Qed.

End naturalDeduction.