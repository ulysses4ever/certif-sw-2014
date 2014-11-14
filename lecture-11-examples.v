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



Theorem plus_plusR : forall n m,
  plusR n m (n + m).
  induction n. 
  auto. simpl. auto.
Qed.

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
  induction 1.
  auto. simpl. auto. 
Qed.

Example four_plus_three' : plusR 4 3 7.
  apply PlusS.
  apply PlusS.
  apply PlusS.
  apply PlusS.
  apply PlusO.
  (* manual search *)

Restart.
  info_auto.


Qed.


Print four_plus_three'.

Example five_plus_three : plusR 5 3 8.
  auto 6.

Restart.
  info_auto 6.

Qed.

(* Backtracking and Unification *)

Example seven_minus_three : 
    exists x, x + 3 = 7.
  exists 0.
  Restart.
  exists 4.
  reflexivity.
Qed.  

Example seven_minus_three' : 
   exists x, plusR x 3 7.
 eexists.
  apply PlusS.
  apply PlusS.
  apply PlusS.
  apply PlusS.
  apply PlusO.
Qed.

Notation "[ x ]" := 
  (ex_intro _ x _).

Print seven_minus_three'.

Example seven_minus_three'' : 
   exists x, plusR x 3 7.
  info_eauto 6.
Qed.
Print seven_minus_three''.


Example seven_minus_four' : exists x, plusR 4 x 7.
  eauto 6.
Qed.

Print seven_minus_four'.

(* Unification for functional definitions *)

SearchRewrite (O + _).

Hint Immediate plus_O_n.

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
  
  intros. simpl. auto.
Qed.  

Hint Resolve plusS.

Example seven_minus_three''' : 
       exists x, x + 3 = 7.
  info_eauto 6.
Qed.

Print seven_minus_three'''.

Example seven_minus_four : exists x, 4 + x = 7.
  eauto 6.
Qed.

Example seven_minus_four_zero : 
       exists x, 4 + x + 0 = 7.
  eauto 6.
Abort.

Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
  intros.  omega.
Qed. 

Print plusO.

Hint Resolve plusO.

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
  eauto 6.
Qed.

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

Example eval1 : 
  forall var, eval var 
   (Plus Var (Plus (Const 8) Var)) 
   (var + (8 + var)).
  info_auto.
Qed.

Example eval1' : forall var, 
  eval var (Plus Var (Plus (Const 8) Var)) 
            (2 * var + 8).
  auto.
Abort.

Theorem EvalPlus' : 
   forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  intros.
  rewrite <- H1.
  auto.
Qed.

Hint Resolve EvalPlus'.

Hint Extern 1 (_ = _) => abstract omega.

Example eval1' : forall var, 
   eval var (Plus Var (Plus (Const 8) Var)) 
   (2 * var + 8).
  info_eauto.
Qed.

Print eval1'.

Example synthesize1 : exists e, 
   forall var, eval var e (var + 7).
  eauto.
Qed.

Print synthesize1.

Example synthesize2 : exists e, 
   forall var, eval var e (2 * var + 8).
  eauto.
Qed.

Print synthesize2.

Example synthesize3 : exists e, 
     forall var, eval var e (30 * var + 42).
  eauto 32.
Qed.

Print synthesize3.

Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
  intros. rewrite H. auto.
Qed.


Hint Resolve EvalConst'.

Theorem zero_times : forall n m r,
  r = m
  -> r = 0 * n + m.
  simpl. auto.
Qed.


Hint Resolve zero_times.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
  intros. rewrite <- H. auto.
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
  intros.
  induction e; eauto.
  destruct IHe1 as [k1 [n1 H1]].
  destruct IHe2 as [k2 [n2 H2]].
  eauto. 
Qed.


