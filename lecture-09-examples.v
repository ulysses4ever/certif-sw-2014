Require Import Arith List Coq.Program.Equality.

Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, 
             A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) 
       n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
      | Nil => ls2
      | Cons _ x ls1' => Cons x (app ls1' ls2)
    end.

  Print app.

  Fixpoint inject (ls : list A) : 
                   ilist (length ls) :=
    match ls with
      | nil => Nil
      | h :: t => Cons h (inject t)
    end.

  Print inject.
  
  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject t
    end.

  Print unject.

  Theorem inject_inverse : 
         forall ls, unject (inject ls) = ls.
  Proof.
    induction ls; try (simpl; rewrite IHls); reflexivity.
  Qed.

  (* Stating theorems problem: unject_inverse *)

(* 
  Theorem unject_inverse : 
     forall n (ls: ilist n), ls = inject (unject ls).
 *)  

  Lemma unject_length : 
   forall n (ls: ilist n),  length(unject ls) = n.
  Proof.
    induction ls; try (simpl; rewrite IHls); reflexivity.
  Qed.  

(* 
  Theorem unject_inverse : 
     forall n (ls: ilist n), ls = inject (unject ls).
 *)  

  Theorem unject_inverse : 
    forall n (ls: ilist n) 
              (pf: length(unject ls) = n),
          ls = match pf in (_ = n) 
                        return ilist n with
               | eq_refl => inject (unject ls)
               end.
  Proof.
    induction ls.
    simpl.
    intros.
    rewrite (UIP_refl _ _ pf).
    reflexivity.
    simpl.
    intros.
    inversion pf.
    rewrite (IHls H0) at 1.
    generalize (inject (unject ls)).
    generalize H0 pf.
    rewrite H0.
    intros.
    repeat rewrite (UIP_refl _ _ _).
    reflexivity.
  Qed.

  Print unject_inverse.


(* Implementing hd *)

(*  
  Definition hd n (ls : ilist (S n)) : A :=
    match ls with
    | Nil => ???
    | Cons _ h _ => h
    end.  
*)  

  Definition hd1 n (ls : ilist (S n)): A :=
    match ls with
    | Cons _ h _ => h
    end.

  Print hd1.
  Print id.

  Definition hd2 n (ls : ilist (S n)): A :=
    match ls in (ilist n') 
       return (match n' with O => unit | S _ => A end) with
    | Nil => tt
    | Cons _ h _ => h
    end.

  Print hd2.

  Definition hd3 n (ls : ilist (S n)): A :=
    match ls in (ilist n') return (
         match n' return ilist n' -> Type with
         | O => fun _ : ilist 0 => unit
         | S n1 => fun _ : ilist (S n1) =>  A
         end ls
          ) with
    | Nil => tt
    | Cons _ h _ => h
    end.
  
  Print hd3.
  
  Definition hd4 n (ls : ilist (S n)):=
    match ls with
    | Nil => tt
    | Cons _ h _ => h
    end.
  Check hd4.

  Print hd4.
  
(* Getting elements *)  

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Check fin 3.
  Check (First 2).
  Check (Next (First 1)).
  Check (Next (Next (First 0))).

(*
  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
      | Nil => fun idx => tt
      | Cons _ x ls' => fun idx =>
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.
*)
(*  Fixpoint get n (ls : ilist n) : fin n -> A :=
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
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.
*)
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
(*
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
             return (fin (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.
*)
  
End ilist.

Arguments Nil [A].
Arguments First [n].

Check Cons 0 (Cons 1 (Cons 2 Nil)).

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) First.

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next First).

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next (Next First)).

(* Implementing map *) 

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) : ilist B n :=
    match ls with
      | Nil => Nil
      | Cons _ x ls' => Cons (f x) (imap ls')
    end.

  Theorem get_imap : 
     forall n (idx : fin n) (ls : ilist A n),
          get (imap ls) idx = f (get ls idx).
  Proof.
    induction ls; dependent destruction idx.
    reflexivity.
    apply IHls.
  Qed.    

End ilist_map.

