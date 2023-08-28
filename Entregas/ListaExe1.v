(* Nenhum outro arquivo deve ser importado.

Nome: Bruno Rafael dos Santos *)

Require Import Coq.Arith.PeanoNat.

(* Podemos definir uma representação binária dos números naturais por meio de dois 
construtores que representam 0s e 1s (B0 e B1), e um marcador de final da sequência Z. 

Por exemplo:


        decimal               Binary                          unary
           0                    B0 Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

Note que o bit menos significativo fica a esquerda da sequência.

*)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(* Complete as definições abaixo, sendo incr uma função que incrementa um número
binário e bin_to_nat a função que converte um binário em natural: *)

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 (Z)
  | B0 m => B1 m
  | B1 m => B0 (incr m)
  end.

Compute incr (B1 (B1 Z)).

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B0 n => 0 + 2*(bin_to_nat n)
  | B1 n => 1 + 2*(bin_to_nat n)
  end.
(* Declare uma função que converta natural para binário: *)

Compute bin_to_nat(incr (B1 (B1 Z))).
Compute bin_to_nat(B1 (B1 Z)).

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n => incr (nat_to_bin n)
  end.

Compute nat_to_bin(8).

(* Prove que as tranformações definididas no diagrama abaixo são válidas: 

                           incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

*)    

Lemma succ_plus_r: forall n m : nat,
  S(n + m) = n + (S m).
Proof.
  intros. induction n as [|k].
  - simpl. reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros. induction b as [|k'|k''].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl (incr (B1 k'')). simpl (bin_to_nat (B0 (incr k''))).
  rewrite IHk''.
  simpl (bin_to_nat (B1 k'')).
  rewrite succ_plus_r. simpl (1 + bin_to_nat k'' + 0).
  reflexivity.
Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros. induction n as [|k].
  - simpl. reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr.
    rewrite IHk. simpl. reflexivity.
Qed.