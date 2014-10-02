
(* Parameterized types *)

Inductive prod (X Y : Set) : Set :=
  pair : X -> Y -> prod X Y.

Check pair.
(* : forall X Y : Set, X -> Y -> prod X Y *)

Check (pair nat nat O (S(S O))).
(* : prod nat nat *)

Arguments pair {X} {Y} _ _.

Check (pair O (S(S O))).

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
match ls with
| Nil => O
| Cons _ ls' => S (length T ls')
end.

Reset list.

Set Implicit Arguments.

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

End list.

Check length.
(* 
 : forall T : Set, list T -> nat 
*)

(*
Check (length nat (Nil nat)).
Check (length nat (Cons nat O (Nil nat))).
*)

Arguments Nil [T].

Check length Nil.