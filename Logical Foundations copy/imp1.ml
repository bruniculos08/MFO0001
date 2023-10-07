
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> True
          | S _ -> False)
  | S n' -> (match m with
             | O -> False
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> True
  | S n' -> (match m with
             | O -> False
             | S m' -> leb n' m')

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb1 : ascii -> ascii -> bool **)

let eqb1 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb0 a0 b0 with
                                       | True -> eqb0 a1 b1
                                       | False -> False with
                                 | True -> eqb0 a2 b2
                                 | False -> False with
                           | True -> eqb0 a3 b3
                           | False -> False with
                     | True -> eqb0 a4 b4
                     | False -> False with
               | True -> eqb0 a5 b5
               | False -> False with
         | True -> eqb0 a6 b6
         | False -> False with
   | True -> eqb0 a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb2 : string -> string -> bool **)

let rec eqb2 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb1 c1 c2 with
        | True -> eqb2 s1' s2'
        | False -> False))

type 'a total_map = string -> 'a

(** val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1 **)

let t_update m x v x' =
  match eqb2 x x' with
  | True -> v
  | False -> m x'

type state = nat total_map

type aexp =
| ANum of nat
| AId of string
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BNeq of aexp * aexp
| BLe of aexp * aexp
| BGt of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

(** val aeval : state -> aexp -> nat **)

let rec aeval st = function
| ANum n -> n
| AId x -> st x
| APlus (a1, a2) -> add (aeval st a1) (aeval st a2)
| AMinus (a1, a2) -> sub (aeval st a1) (aeval st a2)
| AMult (a1, a2) -> mul (aeval st a1) (aeval st a2)

(** val beval : state -> bexp -> bool **)

let rec beval st = function
| BTrue -> True
| BFalse -> False
| BEq (a1, a2) -> eqb (aeval st a1) (aeval st a2)
| BNeq (a1, a2) -> negb (eqb (aeval st a1) (aeval st a2))
| BLe (a1, a2) -> leb (aeval st a1) (aeval st a2)
| BGt (a1, a2) -> negb (leb (aeval st a1) (aeval st a2))
| BNot b1 -> negb (beval st b1)
| BAnd (b1, b2) ->
  (match beval st b1 with
   | True -> beval st b2
   | False -> False)

type com =
| CSkip
| CAsgn of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

(** val ceval_step : state -> com -> nat -> state option **)

let rec ceval_step st c = function
| O -> None
| S i' ->
  (match c with
   | CSkip -> Some st
   | CAsgn (l, a1) -> Some (t_update st l (aeval st a1))
   | CSeq (c1, c2) ->
     (match ceval_step st c1 i' with
      | Some st' -> ceval_step st' c2 i'
      | None -> None)
   | CIf (b, c1, c2) ->
     (match beval st b with
      | True -> ceval_step st c1 i'
      | False -> ceval_step st c2 i')
   | CWhile (b1, c1) ->
     (match beval st b1 with
      | True ->
        (match ceval_step st c1 i' with
         | Some st' -> ceval_step st' c i'
         | None -> None)
      | False -> Some st))
