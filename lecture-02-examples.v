(* Propositions as types in Coq *)

Check (fun x: nat => x).
Check (fun x: True => x).
Check I.
Check (fun x: False => I).

Print True.
Print False.

Theorem bad: False -> 2 + 2 = 5.
Proof.
  intro H.
  destruct H.
Qed.

Theorem mp: forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q H1 H2. apply H1. exact H2.
Qed.

Print mp.

Theorem mp2: forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q H1 H2. apply H1 in H2. exact H2.
Qed.

Print mp2.

Theorem mp3: forall P Q: Prop, (P -> Q) -> P -> Q.
Proof.
  auto.
Qed.

Print mp3.

(* Defining types & functions *)

Inductive weapon: Set := rock | paper | scissors.

Check rock.

Definition next_weapon (w: weapon): weapon :=
match w with
| rock => paper
| paper => scissors
| scissors => rock
end.

Eval simpl in next_weapon rock.
Eval simpl in next_weapon (next_weapon rock).

Definition wpn_beats (w1 w2: weapon): Prop := w2 = next_weapon w1.

Example test_wpn_next2: next_weapon (next_weapon rock) = scissors.
  simpl.
  Restart.
  reflexivity.
Qed.

Example ex1: ~ wpn_beats rock scissors.
  compute.
  intro.
  Restart.
  discriminate.
Qed.

(* Rewriting *)

Theorem wpn_eq_next: forall w1 w2: weapon, w1 = w2 -> next_weapon w1 = next_weapon w2.
  intros w1 w2 H.
  rewrite -> H.
  reflexivity.
Qed.

(* Case analysis *)

Theorem wpn_next3: forall w: weapon, next_weapon (next_weapon (next_weapon w)) = w.
  intros w.
  destruct w; reflexivity.
Qed.

Theorem wpn_eq_next_rev: forall w1 w2: weapon, next_weapon w1 = next_weapon w2 -> w1 = w2.
  intros w1 w2 H.
  destruct w1. 
  destruct w2. reflexivity. discriminate. discriminate.
  destruct w2. discriminate. reflexivity. discriminate.
  destruct w2. discriminate. discriminate. reflexivity. 

  Restart. 

  intros w1 w2.
  destruct w1; destruct w2; reflexivity || discriminate.
Qed.

Theorem wpn_beats_thm: forall w1 w2 w3: weapon, wpn_beats w1 w2 -> wpn_beats w2 w3 -> wpn_beats w3 w1.
  intros w1 w2.
  destruct w1; destruct w2; destruct w3; reflexivity || discriminate. 
Qed.

Theorem wpn_beats_dec: forall w1 w2: weapon, w1 = w2 \/ wpn_beats w1 w2 \/ wpn_beats w2 w1.
  intros.
  destruct w1; destruct w2; try (left; reflexivity); right; (left; reflexivity) || (right; reflexivity).
Qed.
