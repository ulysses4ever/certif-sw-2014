Require Import Arith List.

Set Implicit Arguments.

(* Heterogeneous lists: definition *)

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A),
            B x -> hlist ls -> hlist (x :: ls).

End hlist.

Check hlist.
Check HNil.
Check HCons.


Arguments HNil [A B].
Check HNil.

Arguments HCons [A B x ls _ _].
Check HCons.

Definition someTypes : list Set :=
   nat :: bool :: bool :: (nat * bool)%type :: nil.

Definition someValues :
  hlist (fun T : Set => T) someTypes :=
  HCons 5 (HCons true (HCons false (HCons (2, true) HNil))).

Definition somePairs :
  hlist (fun T : Set => T * T)%type someTypes :=
  HCons (1, 2) (HCons (true, false) (HCons (true, true)
             (HCons ((3, true), (1, false)) HNil))).

Check someValues.
Print someValues.

Check somePairs.
Print somePairs.
Check (1, 2, 3, 4).

(* Access to elements *)

Section member.
  Variable A : Type.
  Variable B : A -> Type.

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  

  Fixpoint hget ls (mls : hlist B ls) :
    member ls -> B elm :=
    match mls with
      | HNil => fun mem => 
         match mem in member ls' return (
               match ls' with 
                | nil => B elm
                | _ :: _ => unit
               end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
         end
      | HCons _ _ x mls' => fun mem => 
         match mem in member ls' return (
                match ls' with
                | nil => Empty_set
                | x' :: ls'' => B x' -> 
                      (member ls''-> B elm) -> B elm
                end
               ) with
          | HFirst _ => fun t _ => t
          | HNext _ _ mem' => fun _ get_mls' 
                 => get_mls' mem' 
         end x (hget mls')
          
    end.
      

End member.

Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls _].

Eval simpl in 
   hget someValues HFirst.

Print someValues.

Eval simpl in 
  hget someValues (HNext HFirst).

Eval simpl in 
  hget someValues (HNext (HNext HFirst)).


Eval simpl in 
  hget somePairs (HNext (HNext HFirst)).

(* Reminder: ilist *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, 
             A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
      | Nil => fun idx =>
        match idx in fin n' 
                 return (match n' with
                         | O => A
                         | S _ => unit
                         end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
       match idx in fin n' 
        return ilist (pred n') -> A with
        | First _ => fun _ => x
        | Next _ idx' => fun ls' => get ls' idx'
        end ls'
    end.
End ilist.

(* Recursive definitions: ilists *)

Section filist.
  Variable A : Set.

  Fixpoint filist (n : nat) : Set :=
    match n with
      | O => unit
      | S n' => A * filist n'
    end%type.

  Fixpoint ffin (n : nat) : Set :=
    match n with
      | O => Empty_set
      | S n' => option (ffin n')
    end.

  Fixpoint fget (n : nat) : filist n -> ffin n -> A :=
    match n with
      | O => fun _ idx => match idx with end
      | S n' => fun ls idx =>
        match idx with
          | None => fst ls
          | Some idx' => fget n' (snd ls) idx'
        end
    end.

End filist.

Arguments fget [A n _ _ ].

Check filist.
Check fget.

Definition ls : 
  filist nat 3 :=  (2, (1, (4, tt))).

Check (Some (Some None)): ffin 3.

Check (Some (Some None)): ffin 5.

Check fget ls (Some (Some None)).

Eval simpl in 
  fget ls (Some (Some None)).

(* Heterogeneous lists: recursive definition *)

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
    end%type.

  Variable elm : A.

  Fixpoint fmember (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + fmember ls'
    end%type.


Fixpoint fhget (ls : list A) : 
   fhlist ls -> fmember ls -> B elm :=
    match ls with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx => 
        match idx with
        | inl pf => match pf  with 
                    | eq_refl => fst mls
                    end
        | inr idx' => fhget ls' (snd mls) idx'
        end
    end.  

End fhlist.

Arguments fhget [A B elm ls _ _].

Check fhlist.

Definition types := nat :: bool :: nat :: nil.
Check types.

Definition fhls :
  fhlist (fun T: Set => T) types :=
  (3, (true, (5, tt))).

Check fhget fhls (inl eq_refl).

Eval simpl in fhget fhls (inl eq_refl).
Eval simpl in fhget fhls (inr (inl eq_refl)).
Eval simpl in fhget fhls (inr (inr (inl eq_refl))).

Check fmember.

Definition fmem1 : fmember nat types :=
  inl eq_refl.

Check inr (inl eq_refl).

Definition fmem2 : fmember bool types :=
   inr (inl eq_refl).

Definition fmem3 : fmember nat types :=
   inr (inr (inl eq_refl)).
