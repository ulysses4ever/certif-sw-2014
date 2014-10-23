Require Import Bool List.

Set Implicit Arguments.

Inductive exp: Set :=
| Nat: nat -> exp
| Bool: bool -> exp
| Plus: exp -> exp -> exp
| And: exp -> exp -> exp.

Check Plus (Bool true) (Nat 8).

Inductive type := TNat | TBool.

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
    hasType e t1 -> forall t2, hasType e t2 -> t1 = t2.
  induction 1; inversion 1; auto.
Qed.

Hint Resolve hasType_det.

(* Awful completely unstructured proof *)
Definition typeCheck_awful : forall e , {t | hasType e t} + {forall t, ~ hasType e t}.
  induction e.
  left.
  exists TNat. auto.
  left.
  exists TBool. auto.
  destruct IHe1; destruct IHe2.
  destruct s. destruct x. destruct s0. destruct x.

  left. exists TNat. auto.

  right. intros. intro. inversion H. 
  assert(TNat = TBool). eauto. discriminate.

  right. intros. intro. inversion H.
  assert(TNat = TBool). eauto. discriminate.

  right. intros. intro. inversion H. eapply n. apply H4.
  
  right. intros. intro. inversion H. eapply n. apply H2.
  
  right. intros. intro. inversion H. eapply n. apply H2.
  
  destruct IHe1; destruct IHe2.
  destruct s. destruct x. destruct s0.  destruct x.
  
  right. intros. intro. inversion H. 
  assert (TBool=TNat). eauto. discriminate.
  
  right. intros. intro. inversion H. 
  assert (TBool=TNat). eauto. discriminate.

  destruct s0. destruct x. 

  right. intros. intro. inversion H. 
  assert (TBool=TNat). eauto. discriminate.
  
  left. exists TBool. auto.

  right. intros. intro. inversion H. eapply n. eapply H4.

  right. intros. intro. inversion H. eapply n. eapply H2.

  right. intros. intro. inversion H. eapply n. eapply H2.
Defined.

Definition typeCheck : 
   forall e , {t | hasType e t} + {forall t, ~ hasType e t}.
refine(fix F (e:exp): {t | hasType e t} + {forall t, ~ hasType e t} :=  
   match e return {t | hasType e t} + {forall t, ~ hasType e t} with 
  | Nat n => inleft _ (exist _ TNat _)
  | Bool b => inleft _ (exist _ TBool _)
  | Plus e1 e2 => 
    match F e1 with
    | inright _ => inright _ _
    | inleft (exist t1 _) => 
        match F e2 with
        | inright _ => inright _ _
        | inleft (exist t2 _) => 
           match eq_type_dec t1 TNat with
           | left _ => match eq_type_dec t2 TNat with
                       | left _ => inleft _ (exist _ TNat _)
                       | right _ => inright _ _
                       end
           | right _ => inright _ _
           end
        end
    end
  | And e1 e2 => _
  end). 
  auto. auto. 
  rewrite e0 in h.
  rewrite e3 in h0.
  auto.
  
  intros. intro. inversion H. apply n. 
  inversion h0. auto. auto.
  inversion H4; inversion h0; congruence.
  inversion H4; inversion h0; congruence.
  auto.
  intros. intro. apply n.
  inversion H; inversion h; auto.
  inversion H2; inversion h; congruence.
  inversion H2; inversion h; congruence.
  
  intros. intro. eapply n. inversion H. apply H4. 
  intros. intro. eapply n. inversion H. apply H2.

  
Admitted.

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

Definition typeCheck' : forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
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
    end).

Admitted.