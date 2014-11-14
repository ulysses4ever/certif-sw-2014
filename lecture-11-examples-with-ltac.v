Require Import List Omega.
Set Implicit Arguments.

(* Part 1: introduction to proof search *)

Print plus.

Example four_plus_three : 4 + 3 = 7.
  reflexivity.
Qed.

Print four_plus_three.

Inductive plusR : 
      nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

Hint Constructors plusR.

Ltac crush' := intros; simpl; 
  match goal with
  | [ H : ex _ |- _] => destruct H
  | [ H : _ |- _ ] => try (rewrite <- H || rewrite H)
  | _ => idtac
  end; try omega; eauto.

Ltac crush := repeat crush'.

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
  induction n; crush.
Qed.

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
  induction 1; crush.
Qed.

Hint Immediate plus_O_n.

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
  crush.  
Qed.  

Hint Resolve plusS.

Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
  crush.
Qed. 

Print plusO.

Hint Resolve plusO.


(* Path 2: Synthesizing Expressions *)

Inductive exp : Set :=
| Const : nat -> exp
| Var : exp
| Plus : exp -> exp -> exp.

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

Hint Constructors eval.

Theorem EvalPlus' : 
   forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  crush.
Qed.

Hint Resolve EvalPlus'.

Hint Extern 1 (_ = _) => abstract omega.

Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
  crush.
Qed.

Hint Resolve EvalConst'.

Theorem zero_times : forall n m r,
  r = m
  -> r = 0 * n + m.
  crush.
Qed.


Hint Resolve zero_times.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
  crush.
Qed.


Hint Resolve EvalVar'.

Theorem plus_0 : forall n r,
  r = n
  -> r = n + 0.
  auto.
Qed.

Theorem times_1 : forall n, n = 1 * n.
  auto.
Qed.

Hint Resolve plus_0 times_1.

Require Import Arith Ring.

Theorem combine : forall x k1 k2 n1 n2,
  (k1 * x + n1) + (k2 * x + n2) = (k1 + k2) * x + (n1 + n2).
  intros; ring.
Qed.

Hint Resolve combine.

Theorem linear : forall e, exists k, exists n,
  forall var, eval var e (k * var + n).
  induction e; crush. 
Qed.


