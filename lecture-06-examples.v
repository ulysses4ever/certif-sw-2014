Require Import NArith.
Require Import List.

(* Definitions of pred: parameters, return types, styles *)

Definition pred (n: nat): nat :=
match n with
| O => O
| S n' => n'
end.

Check pred.
Print pred.

Definition pred' (n: nat): nat.
  destruct n as [ | n0].
  exact 0.
  exact n0.
Defined.

Definition pred'': forall n:nat, nat.
  intro n.
  destruct n as [ | n0].
  exact 0.
  exact n0.
Defined.

Definition pred''': nat -> nat.
  destruct 1 as [ | n0].
  exact 0.
  exact n0.
Defined.

Definition pred'''': nat -> nat.
  exact (fun n =>
   match n with
   | O => O
   | S n' => n'
   end).
Defined.

Definition pred''''': nat -> nat.
  refine (fun n =>
   match n with
   | O => _
   | S n' => _
   end).
  exact O.
  exact n'.
Defined.

Print pred'''''.

Eval compute in pred''''' 6.
Eval compute in pred''''' 0.

(* Problem 1: 0 => 0 oddity *)

Lemma zgtz: 0 > 0 -> False.
  inversion 1.
Qed.

Print sig.

(*
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x | P x}
*)

Definition pred_strong1 (s: {n: nat | n > 0}) : nat := 
match s with
| exist O pf => match zgtz pf with end
| exist (S n') _ => n'
end.

Definition pred_strong1' (s: {n: nat | n > 0}) : nat.
exact (match s with
| exist O pf => match zgtz pf with end
| exist (S n') _ => n'
end).
Defined.

SearchPattern (_ > _). (* Require Import NArith. *)

Check Gt.gt_Sn_O 1.
(* 
Gt.gt_Sn_O 1
     : 2 > 0
*)

Eval compute in pred_strong1 (exist _ 2 (Gt.gt_Sn_O 1)).

(* Problem 2: precondition & result specification *)

Definition pred_strong2: forall n: nat, n > 0 -> {m: nat | n = S m}.
  intros.
  destruct n as [ | n'].
  elimtype False.
  inversion H.
  exists n'.
  reflexivity.
Defined.

Check pred_strong2.

Eval compute in pred_strong2 2 (Gt.gt_Sn_O 1).
(* 
  = exist (fun m : nat => 2 = S m) 1 eq_refl
     : {m : nat | 2 = S m}
*)

Notation "[ e ]" :=(exist _ e _).

Eval compute in pred_strong2 10 (Gt.gt_Sn_O 9).

Definition pred_strong3: forall n: nat, n > 0 -> {m: nat | n = S m}.
  refine 
   (fun n => match n with
     | O => fun pf => False_rec _ _
     | S n' => fun _ => exist _ n' _
     end).
(*
2 subgoals, subgoal 1 (ID 150)
  
  n : nat
  pf : 0 > 0
  ============================
   False

subgoal 2 (ID 153) is:
 S n' = S n' *)
  inversion pf. reflexivity.
Defined.

Print False_rec.
(* False_rec = fun P : Set => False_rect P
     : forall P : Set, False -> P *)

(* Problem 3: what if there is no proof for n>0? 
  We should allow to fail gracefully. *)

(* Version 1: result is a value or not a value *)
Definition pred_strong4: forall n: nat, {m: nat | n = S m} + {n = 0}.
  refine 
   (fun n => match n with
     | O => inright _ _
     | S n' => inleft _ _ 
     end).
  reflexivity.
  exists n'.
  reflexivity.
Defined.

Print sumor.

(*
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
*)

Eval compute in pred_strong4 10.
(*
 = inleft [9]
     : {m : nat | 10 = S m} + {10 = 0}
*)
Eval compute in pred_strong4 0.
(*
 inright eq_refl
     : {m : nat | 0 = S m} + {0 = 0}
*)

Notation "!!" := (inright _ _).
Notation "[[ x ]]" := (inleft _ [ x ]).

Eval compute in pred_strong4 10.
Eval compute in pred_strong4 0.

(* Decidable Proposition Types *)

Print sumbool.
(*
Inductive sumbool (A B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
*)

Definition eq_nat_dec: forall n m: nat, {n=m} + {n <> m}.
  refine (fix f (n m: nat): {n=m} + {n <> m} :=
    match n, m with
    | O, O => _
    | S n', S m' => _
    | _, _ => _
    end).
(*
  f : forall n m : nat, {n = m} + {n <> m}
  n : nat
  m : nat
  ============================
   {0 = 0} + {0 <> 0}

subgoal 2 (ID 231) is:
 {0 = S n0} + {0 <> S n0}
subgoal 3 (ID 233) is:
 {S n' = 0} + {S n' <> 0}
subgoal 4 (ID 235) is:
 {S n' = S m'} + {S n' <> S m'}
*)
  left. reflexivity.
  right. discriminate.
  right. discriminate.
  destruct f with (n') (m').
  left. rewrite e. reflexivity.
  right. intro. inversion H. contradiction.
Defined.

Definition eq_nat_dec': forall n m: nat, {n=m} + {n <> m}.
  refine (fix f (n m: nat): {n=m} + {n <> m} :=
    match n, m with
    | O, O => left _  _
    | S n', S m' => if f n' m' then (left _ _) else (right _ _)
    | _, _ => right _ _
    end);  congruence.
Defined.

Definition eq_nat_dec'': forall n m: nat, {n=m} + {n <> m}.
  decide equality.
Defined.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).

Eval compute in eq_nat_dec 2 3.
Eval compute in eq_nat_dec 10 10.

(* Using decidability results:
1) 
match eq_nat_dec x y with
| left _ => _
| right _ => _
end

2) 
if eq_nat_dec x y then _ else _

3) 
destruct (eq_nat_dec x y).
*)

(* List membership *)

Set Implicit Arguments.

Section In_dec.
  Variable A: Set.
  Variable A_eq_dec: forall x y: A, {x=y} + {x<>y}.
  Definition In_dec: forall (x: A) (ls: list A), {In x ls} + {~ In x ls}.
    refine (fix f (x: A) (ls: list A): {In x ls} + {~ In x ls} :=
       match ls with
       | nil => right _ _
       | x' :: ls' => if A_eq_dec x x' then Yes else 
                        if f x ls' then Yes else No
       end); simpl; auto; intuition.
  Defined.
End In_dec.

Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).
Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).
