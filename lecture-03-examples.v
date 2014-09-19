(* Natural numbers *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition pred (n: nat): nat :=
match n with
| O => O
| S n' => n'
end.

Eval simpl in pred (S (S (S O))).

(* Injection and discriminate magic *)

Theorem S_inj: forall n m: nat, S n = S m -> n = m.
  injection 1. 
  (* Goal: n=m -> n = m *)
  trivial.
  Restart.
  congruence. (* complete decision procedure for the theory of equality, 
                 uninterpreted functions and inductive types *)
  Restart.
  intros n m H.
  assert (H1: forall n: nat, n = pred (S n)). reflexivity.
  rewrite -> H1 with (n).
  rewrite -> H1 with (m).
  rewrite -> H.
  reflexivity.
  Restart. 
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.

Inductive weapon: Set := rock | paper | scissors.

Definition toProp(w: weapon): Prop :=
match w with
| rock => True
| _ => False
end.

Theorem discr: rock <> paper.
  intro.
  change(toProp paper).
  rewrite <- H.
  simpl.
  apply I.
Qed.  

(* Fixpoints, terminality *)

Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

Theorem O_plus_n : forall n : nat, plus O n = n.
  intro.
  reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
  intro.
  destruct n. reflexivity. simpl.
  (*
      n : nat
  ============================
   S (plus n O) = S n
  *)
  Restart.
  intro.
  induction n.
  reflexivity. 
  (* IHn : plus n O = n 
  ============================
   plus (S n) O = S n
  *)
  simpl. rewrite -> IHn. reflexivity.
Qed.

(* nat_ind : ∀ P : nat → Prop, P O → (∀ n : nat, P n → P (S n)) → ∀ n : nat, P n *)

(* Data structures *)

Inductive nat_pair: Set :=
| Pair: nat -> nat -> nat_pair.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.


(*
nat_list_ind : 
   ∀ P : nat_list → Prop, 
   P NNil → (∀ (n : nat) (n0 : nat_list), P n0 → P (NCons n n0 )) →
   ∀ n : nat_list, P n
*)

Fixpoint nlength (ls: nat_list): nat :=
match ls with
| NNil => O
| NCons _ ls' => S (nlength ls')
end.

Eval simpl in nlength (NCons (S (S (S O))) (NCons O NNil)).

Fixpoint napp (ls1 ls2: nat_list): nat_list :=
match ls1 with
| NNil => ls2
| NCons n ls1' => NCons n (napp ls1' ls2)
end.

Theorem nlength_napp: forall ls1 ls2: nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
  intros.
  induction ls1; 
  simpl. reflexivity.
  simpl. rewrite -> IHls1. reflexivity.
Qed.

