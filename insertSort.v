Require Import List.
Require Import ZArith.
Open Scope Z_scope.

(* 1 *)

(* Property of sorted list *)

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Theorem sorted_inv : forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
Proof.
 inversion 1; auto with sort.
Qed.

(* 2 *)

(*  Number of occurences of z into l *)

Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S (nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.

Eval compute in (nb_occ 3 (3 :: 7 :: 3 :: nil)).

Eval compute in (nb_occ 36725 (3 :: 7 :: 3 :: nil)).

(* Relation "list l' is a permutation of l" and its properties *)

Definition equiv (l l':list Z) := forall z:Z, nb_occ z l = nb_occ z l'.

Check equiv.

Hint Unfold equiv.

Lemma equiv_refl : forall l:list Z, equiv l l.
Proof.
  auto.
Qed.

Lemma equiv_sym : 
  forall l l':list Z, equiv l l' -> equiv l' l.
Proof.
  auto.
Qed.

Lemma equiv_trans :
 forall l l' l'':list Z, equiv l l' -> equiv l' l'' -> equiv l l''.
Proof.
  unfold equiv.
  intros.
  eapply trans_eq; auto.
Qed.

(* Addind new element to equivalent lists *)

Lemma equiv_cons :
 forall (z:Z) (l l':list Z), equiv l l' -> 
                             equiv (z :: l) (z :: l').
Proof.
  unfold equiv.
  intros.
  simpl; destruct (Z_eq_dec z0 z); auto.
Qed.

(* Permuting elements in equivalent lists *)

Lemma equiv_perm :
 forall (a b:Z) (l l':list Z),
   equiv l l' -> 
   equiv (a :: b :: l) (b :: a :: l').
Proof.
  unfold equiv.
  intros.
  simpl; destruct (Z_eq_dec z a); destruct (Z_eq_dec z b); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.

(* 3 *)

(* Inserting element into sorted list *)

Fixpoint ins_sorted (z:Z) (l:list Z) : list Z :=
  match l with
  | nil => z :: nil
  | a :: l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: a :: l'
      | right _ => a :: (ins_sorted z l')
      end
  end.

Eval compute in (ins_sorted 4 (2 :: 5 :: nil)).

Eval compute in (ins_sorted 4 (24 :: 50 ::nil)).

(* ins_sorted: holding equivalence *)

Lemma ins_sorted_equiv : forall (l:list Z) (x:Z), 
                  equiv (x :: l) (ins_sorted x l).
Proof.
 induction l as [|a l0 H]; simpl; auto with sort.
 intros.
 destruct (Z_le_gt_dec x a); auto with sort.
 apply equiv_trans with (a :: x :: l0); auto with sort.
Qed.


(* ins_sorted: holding order *)

Lemma ins_sorted_sorted :
 forall (l:list Z) (x:Z), sorted l -> 
                          sorted (ins_sorted x l).
Proof.
 induction 1; simpl.
 constructor.
 destruct (Z_le_gt_dec x z); auto with sort zarith.
 destruct (Z_le_gt_dec x z1); auto with sort zarith.
 simpl in IHsorted. 
 destruct (Z_le_gt_dec x z2); auto with sort zarith.
Qed.

(* 4 *)

(* Certified sort *)

Definition sort :
  forall l:list Z, 
    {l' : list Z | equiv l l' /\ sorted l'}.
 induction l as [| a l IHl].
 exists (nil (A := Z)); split; auto with sort.
 case IHl; intros l' [H0 H1].
 exists (ins_sorted a l'); split.
 apply equiv_trans with (a :: l'); auto with sort.
 apply ins_sorted_equiv.
 apply ins_sorted_sorted.
 auto.
Defined.

Extraction Language Haskell.
Extraction "insert_sort" ins_sorted sort.
