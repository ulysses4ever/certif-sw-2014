(* Require Import Bool. *)
Require Import List.
Require Import Omega.

(* Propositional logic revisited *)

Print True.

Print False.

Print not. 
(* not = fun A : Prop => A -> False
     : Prop -> Prop
*)

Print and.
(* 
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B
For conj: Arguments A, B are implicit
*)

Print or.
(* Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B
*)

Theorem arith_comm' : forall ls1 ls2 : list nat,
 length ls1 = length ls2 \/ length ls1 + length ls2 = 6 -> length (ls1 ++ ls2 ) = 6 \/ length ls1 = length ls2.
  intuition.
(* H0 : length ls1 + length ls2 = 6
  ============================
   length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2
*)

  SearchAbout length.
  rewrite app_length.
  tauto.
Qed.

Theorem exist1 : exists x : nat, x + 1 = 2.
Proof.
  exists 1.
  reflexivity.
Qed.

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
Proof.
  destruct 1.
(*
  n : nat
  m : nat
  x : nat
  H : n + x = m
  ============================
   n <= m
*)
  rewrite <- H.
  SearchPattern ( _ <= _ + _).
  apply Plus.le_plus_l.
  Restart.
  destruct 1.
  omega. (* Require Import Omega. *)
Qed.

(* Inductive predicates: examples *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
Proof.
  destruct 1.
  SearchAbout (_ + 0).
  apply plus_0_r.
  Restart.
  destruct 1.
  auto.
Qed.

Theorem is_Zero_contra : isZero 1 -> False.
Proof.
  destruct 1. (* no hypotheses *)
  Restart.
  inversion 1.
Qed.

Section twoEls.
  Variable A : Type.

  Inductive twoEls : list A -> Prop :=
  | TwoEls : forall x y, twoEls (x :: y :: nil).

  Theorem twoEls_nil : ~twoEls nil.
    inversion 1.
  Qed.

  Theorem twoEls_two : forall ls, twoEls ls -> length ls = 2.
    inversion 1.
    reflexivity.
  Qed.
End twoEls.

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
  constructor.
Qed.

Theorem even_4 : even 4.
  constructor; constructor; constructor.
Qed.

Hint Constructors even.

Theorem even_8 : even 8.
  auto.
Qed.

Theorem even_1_contra : even 1 -> False.
  inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
  inversion 1.
  (*
  H : even 3
  n : nat
  H1 : even 1
  H0 : n = 1
  ============================
   False
  *)

  inversion H1.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction 1; auto.
(*
  IHeven : even m -> even (n + m)
  ============================
   even m -> even (S (S n) + m)
*)
  intro.
  simpl.
  constructor.
  apply IHeven. assumption. 
Qed.

