(* Exercise #1 *)

Fact f1: forall A B: Prop, A -> (B -> A).
Proof.
 (* Write proof here and then replace Admitted with Qed *)
Admitted.

Fact f2: forall A B C: Prop, (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
Admitted.

Fact f3: forall x y z: Prop, (x -> (y -> z)) -> ((x -> y) -> (x -> z)).
Proof.
Admitted.

Fact f4: forall A B C: Prop, (A -> B) -> A -> C \/ B.
Proof.
Admitted.

Fact f5: forall A B C: Prop, A /\ B -> A \/ B.
Proof.
Admitted.

Fact f6:  forall A , ~~~ A -> ~ A .
Proof.
Admitted.

Fact f7: forall A B: Prop, ~A -> ~(A /\ B).
Proof. 
Admitted.

Fact f8: forall a, ~ (a /\ ~a).
Proof.
Admitted.

Fact f9: forall T (P: T -> T -> Prop), (exists x, forall y, P x y) -> (forall y, exists x, P x y).
Proof.
Admitted.

(* Exercise #2 

Postulate following facts and prove them (hint: use 'split' tactic for <->):

1. forall A : Prop, A -> A
2. forall A B C : Prop, (A -> B) -> (B -> C) -> A -> C
3. forall A B : Prop, A /\ B <-> B /\ A
4. forall A B : Prop, A \/ B <-> B \/ A
5. forall A : Prop, A -> ~~A
6. forall A B : Prop, (A -> B) -> ~B -> ~A
7. forall A : Prop, ~~(A \/ ~A)
8. forall A B C : Prop, (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C)
9. forall A B C : Prop, (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C)

*)

Parameter X Y : Set.
Parameter A B : X -> Prop.
Parameter R : X -> Y -> Prop.

(* Exercise #3

Postulate following facts and prove them:

1. (forall x : X, A x /\ B x) <-> (forall x : X, A x) /\ (forall x : X, B x)
2. (exists x : X, A x \/ B x) <-> (exists x : X, A x) \/ (exists x : X, B x)
3. (forall x : X, exists y : Y, R x y) -> (exists y : Y, forall x : X, R x y)
4. (exists y : Y, forall x : X, R x y) -> (forall x : X, exists y : Y, R x y)
*)


(* Exercise #4 *)

Definition peirce := forall P Q: Prop, ((P->Q)->P)->P.
Definition classic := forall P: Prop, ~~P -> P.

(* Work out following proof, try to explain evey step. *)
Lemma p2c: peirce -> classic.
Proof.
  unfold classic.
  unfold peirce.
  intros.
  apply H with (P:=P) (Q:=False).
  intros.
  contradiction. 
Qed.

Lemma c2p: classic -> peirce.
Proof.
  (* Write proof here. *)
Admitted.

Theorem pc: peirce <-> classic.
Proof.
  (* Write proof here. *)
Admitted.