Require Import Bool List.

Set Implicit Arguments.

(* === Untyped expressions and typechecking === *)

Inductive exp: Set :=
| Nat: nat -> exp
| Bool: bool -> exp
| Plus: exp -> exp -> exp
| And: exp -> exp -> exp.

Check Plus (Bool true) (Nat 8).

Inductive type := TNat | TBool.

(* Typing rules:

-----------       -------------
Nat n: TNat       Bool b: TBool

e1 : TNat   e2 : TNat
---------------------
  Plus e1 e2 : TNat

e1 : TBool   e2 : TBool
-----------------------
   And e1 e2 : TBool

*)

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n, hasType (Nat n) TNat
| HtPlus : forall e1 e2, 
   hasType e1 TNat -> 
   hasType e2 TNat -> 
   hasType (Plus e1 e2) TNat
| HtBool : forall b, hasType (Bool b) TBool
| HtAnd : forall e1 e2, 
   hasType e1 TBool -> 
   hasType e2 TBool -> 
   hasType (And e1 e2) TBool.

Hint Constructors hasType.

Definition eq_type_dec : 
    forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Lemma hasType_det : forall e t1, 
    hasType e t1 -> forall t2, 
    hasType e t2 -> t1 = t2.
  induction 1; inversion 1; auto.
Qed.

Hint Resolve hasType_det.

Definition typeCheck : 
   forall e , {t | hasType e t} + {forall t, ~ hasType e t}.
refine(fix F (e:exp): {t | hasType e t} + {forall t, ~ hasType e t} :=  
  match e with 
  | Nat n => inleft _ (exist _ TNat _)
  | Bool b => inleft _ (exist _ TBool _)
  | Plus e1 e2 => 
    match F e1 with
    | inright Hn => inright _ _
    | inleft (exist t1 H1) => 
        match F e2 with
        | inright Hn => inright _ _
        | inleft (exist t2 H2) => 
           match eq_type_dec t1 TNat with
           | left Heq1 => match eq_type_dec t2 TNat with
                       | left Heq2 => inleft _ (exist _ TNat _)
                       | right Hn => inright _ _
                       end
           | right Hn => inright _ _
           end
        end
    end
  | And e1 e2 => 
    match F e1 with
    | inright Hn => inright _ _
    | inleft (exist t1 H1) => 
        match F e2 with
        | inright Hn => inright _ _
        | inleft (exist t2 H2) => 
           match eq_type_dec t1 TBool with
           | left Heq1 => match eq_type_dec t2 TBool with
                       | left Heq2 => inleft _ (exist _ TBool _)
                       | right Hn => inright _ _
                       end
           | right Hn => inright _ _
           end
        end
    end
  end); try (rewrite Heq1 in H1; rewrite Heq2 in H2); 
        try (inversion 1; eapply Hn);  
        eauto.
Defined.

Print typeCheck.

Notation "[|| t ||]" := (inleft _ (exist _ t _)).
Notation "!!" := (inright _  _).

Eval compute in typeCheck (Plus (Bool true) (Nat 8)).
Eval compute in typeCheck (Plus (Nat 6) (Nat 8)).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

Definition typeCheck' : 
    forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
  refine (fix F (e : exp) : 
             {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t : type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end); 
    try (rewrite _H in h; rewrite _H0 in h0); 
    try inversion 1; 
    try eapply n; 
    eauto.
Defined.


(* === Evaluation === *)

(* 
1) Type "option t": Some _ | None
2) Type nat + bool: inl _  | inr _
*)

Fixpoint evalu (e: exp): option (nat + bool).
refine(
  match e with
  | Nat n => Some (inl n)
  | Bool b => Some (inr b)
  | Plus e1 e2 => 
     match evalu e1 with
     | Some (inl n1) => 
       match evalu e2 with
       | Some (inl n2) => Some (inl (n1 + n2))
       | Some (inr _) => None
       | None => None
       end
     | Some (inr _) => None
     | None => None
     end
  | And e1 e2 => 
     match evalu e1 with
     | Some (inr b1) => 
       match evalu e2 with
       | Some (inr b2) => Some (inr (b1 && b2))
       | Some (inl _) => None
       | None => None
       end
     | Some (inl _) => None
     | None => None
     end
  end).
Defined.  



Eval compute in evalu (Plus (Nat 6) (Nat 8)).
Eval compute in evalu (Nat 6).
Eval compute in evalu (Plus (Bool true) (Nat 8)).
Eval compute in evalu (And (Bool true) (Bool false)).


(* === Typed expressions and conversion === *)

Inductive texp : type -> Set :=
| NNat: nat -> texp TNat
| NBool: bool -> texp TBool
| NPlus: texp TNat -> texp TNat -> texp TNat
| NAnd: texp TBool -> texp TBool -> texp TBool.


Fixpoint exp2texp (e: exp): 
   forall (t:type), hasType e t -> texp t.
refine (
  match e with
  | Nat n => fun t => 
     match t with
     | TNat => fun H => NNat n
     | TBool => fun H => False_rec _ _
     end
  | Bool b => fun t => 
     match t with
     | TBool => fun H => NBool b
     | TNat => fun H => False_rec _ _
     end
  | Plus e1 e2 => fun t => 
     match t with
     | TBool => fun H => False_rec _ _
     | TNat => fun H => 
            NPlus (exp2texp e1 TNat _)
                  (exp2texp e2 TNat _) 
     end
  | And e1 e2 => fun t => 
     match t with
     | TNat => fun H => False_rec _ _
     | TBool => fun H => 
            NAnd (exp2texp e1 TBool _)
                  (exp2texp e2 TBool _) 
     end
  end); try inversion H; auto.  
Defined.    


Print exp2texp.

Example ht1: hasType (Plus (Nat 6) (Nat 8)) TNat.
auto.
Qed.

Eval compute in  exp2texp ht1.

(* === Evaluation of typed expressions === *)

Definition typeDenote (t: type) : Set :=
match t with
| TNat => nat
| TBool => bool
end.

Fixpoint evalt (t: type) (e: texp t): typeDenote t :=
match e with
| NNat n => n
| NBool b => b
| NPlus e1 e2 => evalt e1 + evalt e2
| NAnd e1 e2 => evalt e1 && evalt e2
end.


Eval compute in  evalt (exp2texp  ht1).

Example ht2: hasType (Plus (Nat 1) (Nat 1)) TNat.
auto.
Qed.

Eval compute in  evalt (exp2texp ht1) + evalt (exp2texp ht2).

(* === Evaluation of untyped expressions revisited === *)

Definition eval (e: exp): option(nat+bool).
refine(
  match typeCheck e with
  | inleft (exist t H) => 
     let v := evalt (exp2texp H) in
        Some _
  | inright _ => None
  end); destruct t; [ left | right ]; exact v.
Defined.


Eval compute in eval (Plus (Nat 6) (Nat 8)).
Eval compute in eval (And (Bool true) ((And (Bool true) (Bool false)))).
Eval compute in eval (Plus (Nat 6) (Bool true)).

