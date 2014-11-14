(* Mutually Inductive Types *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.



Theorem elength_eapp : forall el1 el2 : even_list,
 elength (eapp el1 el2) = 
   plus (elength el1) (elength el2).

  induction el1.
  simpl. intros. reflexivity.
  simpl. intros. (* No induction hypothesis *)
Abort.

Check even_list_ind.

Scheme even_list_mut := 
     Induction for even_list Sort Prop
 with odd_list_mut := 
     Induction for odd_list Sort Prop.

Check even_list_mut.

Ltac crush' := intros; simpl; 
  match goal with
  | [ H : ex _ |- _] => destruct H
  | [ H : _ |- _ ] => try (rewrite <- H || rewrite H)
  | _ => idtac
  end;  eauto.

Ltac crush := repeat crush'.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).

  apply (even_list_mut (fun el1  : even_list => 
   forall el2: even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2))
     (fun ol1  : odd_list => 
   forall el2: even_list,
  olength (oapp ol1 el2) = plus (olength ol1) (elength el2))); crush.
Qed.
