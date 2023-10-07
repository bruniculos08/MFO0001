(** * Métodos Formais - Lista de Exercícios 3 
 Não importar nenhum outro módulo.*)

(* Aluno: Bruno Rafael dos Santos *)

Require Import Coq.Lists.List.
Import ListNotations.


Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


(** O tamanho da lista resultante da concatenação de duas listas é
    igual a soma dos tamanhos das listas, prove esse teorema *)


Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1 as [|h t].
  - simpl. reflexivity.
  - intros. simpl. specialize (IHt l2). rewrite IHt. reflexivity.
Qed.

(** A operação de reverso é distributiva em relação a concatenação, prove 
    esse teorema *)

(* Teorema auxiliar (não quero encher muitos asserts) *)
Theorem app_comm: forall X (l1 l2 l3 : list X), 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1 as [|h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.
    
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1 as [|h1 t1].
  - simpl. assert (forall X (l : list X), l ++ [] = l).
  {
   intro. induction l as [|h t].
    - simpl. reflexivity.
    - simpl. rewrite IHt. reflexivity. 
  }
  specialize (H X (rev l2)). rewrite H. reflexivity.
  - simpl. rewrite IHt1. rewrite app_comm. reflexivity.
Qed.

(** Informalmente podemos dizer, que o seguinte teorema estabelece que a 
    função [fold] é comutativa em relação a concatenação ([++]), prove esse 
    teorema: *)
 
Theorem app_comm_fold :forall {X Y} (f: X->Y->Y) l1 l2 b,
  fold f (l1 ++ l2) b = fold f l1 (fold f l2 b).
Proof.
  intros. induction l1 as [|h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

(** Como visto no módulo [Poly.v], muitas funções sobre listas podem ser 
    implementadas usando a função [fold], por exemplo, a função a função 
    que retorna o número de elementos de uma listas pode ser implementada 
    como: *)

(* Não entendi por que definir com a seguinte função da errado: *)
Definition ret_plus1 {X : Type} (x : X) (n : nat) : nat:=
  plus 1 n.

Check ret_plus1.
Check ((fun X => plus 1)).

Definition fold_length {X : Type} (l : list X) : nat :=
    (* fold (fun X => plus 1) l 0. *)
    fold (ret_plus1) l 0.
  
Compute fold_length([1 ; 2 ; 3]).

(** Prove que [fold_length] retorna a número de elementos de uma lista.
    Para facilitar essa prova demostre o lema [fold_length_head]. Dica
    as vezes a tática [reflexivty] aplica uma simplificação mais agressiva 
    que a tática [simpl], isso seŕá util na prova desse lema. *) 

Lemma fold_length_head : forall X (h : X) (t : list X),
  fold_length (h::t) = S (fold_length t).
Proof.
  (* intros. unfold fold_length. simpl. reflexivity. *)
  intros. induction t as [|h1 t1].
  - reflexivity.
  - reflexivity.
Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros. induction l as [|h t].
  - simpl. unfold fold_length. simpl. reflexivity.
  - simpl. rewrite fold_length_head. rewrite IHt. reflexivity. 
Qed.

(** Também é possível definir a função [map] por meio da função [fold],
    faça essa definição *)

Search (app).

Compute app [1] [2 ; 1].

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun X => app [(f X)]) l [].

Example test_fold_map : fold_map (mult 2) [1; 2; 3] = [2; 4; 6].
Proof. 
  simpl. unfold fold_map. simpl. reflexivity.
Qed.

(** Prove que [fold_map] tem um comportamento identico a [map], defina lemas 
    auxiliares se necessário *)

Theorem fold_nil : forall X Y (f: X -> Y),
  fold_map f [] = [].
Proof.
  intros. unfold fold_map. simpl. reflexivity.
Qed.

Theorem fold_map_head : forall X Y (f: X -> Y) (h: X) (t: list X),
  fold_map f (h::t) = f h :: fold_map f t.
Proof.
  intros. induction t as [|h1 t1]. 
  - rewrite fold_nil. unfold fold_map. simpl. reflexivity.
  - unfold fold_map. simpl (fold (fun X0 : X => app [f X0]) (h :: h1 :: t1) []).
    simpl (f h :: fold (fun X0 : X => app [f X0]) (h1 :: t1) []).
    reflexivity.
Qed.

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  intros. induction l as [|h t].
  - simpl. rewrite fold_nil. reflexivity.
  - simpl. rewrite <- IHt. rewrite fold_map_head. reflexivity.
Qed.

(** Podemos imaginar que a função [fold] coloca uma operação binária entre
    cada elelento de uma lista, por exemplo, [fold plus [1; 2; 3] 0] é igual 
    (1+(2+(3+0))). Da forma que foi declarada a função [fold] a operação 
    binária é executada da direita para esquerda. Declare uma função [foldl]
    que aplique a operação da esquerda para direita: *)

Fixpoint foldl {X Y: Type} (f: Y->X->Y) (b: Y) (l: list X)
                         : Y :=
  match l with 
  | nil => b
  | h :: t => foldl f (f b h) t
  end.

(** Exemplo: [foldl minus 10 [1; 2; 3]] igual (((10-1)-2)-3). *)

Example test_foldl : foldl minus 10 [1; 2; 3] = 4.

Proof.
    simpl. reflexivity.



