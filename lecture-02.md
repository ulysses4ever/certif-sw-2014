## CHC

###Biblio###

* 	Software Foundations, chaps. Basics and Induction (you should work out
	all exercises from these),
* 	Chlipala's book: first half of ch. 3.

Recall the table from last lecture.

`A` — proposition       |     `A` — type
------------------------|---------------------------------------------------
`A` holds.              | `A` is inhabited.
`A` has a proof.        | There are members (or values) of this type `A`.
`A → B` (A implies B).  | Function types: `A → B`.
`A ∧ B` (conjunction).  | `A × B` (product types: records, `struct`'s, etc.)
`A or B` (disjunction). | `A + B` (disjoint sum of sets, C `unions`, etc.)
`False`					| Empty type.
`True`					| One-element set/type.

### Examples for CHC

Following CHC _to prove_ in Coq implies _to build a term_ of some type.
Coq only typechecks the term that we build. If it succeeds then this means
that we have proved corresponding proposition.

Consider following examples using Vernacular command **`Check`** which
shows us types.

	Check (fun x: nat => x).
		: nat -> nat

	Check (fun x: True => x).
		: True -> True
		
	Check I.
		: I: True
		
	Check (fun x: False => I).
		: False -> True
		
Though last example demonstrates proposition which holds (False → True)
and we proved it via supplying corresponding term, a function, we can't
apply this function to smth else as False type is not inhabited.

In Coq we can have

*	functional types,
*	inductive types,

and that's it. We can inspect this with **`Print`** command.

	Print False.
		Inductive False: Prop :=

	Print True.
		Inductive True: Prop := I

Consider following theorem.

	Theorem bad: False -> 2 + 2 = 5.
	Proof.
		intro.			| H: False
		destruct H.		| No more goals.
	Qed.

Tactic `destruct` “looks” inside `H` sees nothing and this usually 
implies everything including our goal. So the prove is done.

	Theorem mp: forall P Q: Prop, (P -> Q) -> P -> Q.
	Proof.
		intros P Q H1 H2.
		apply H1.
		exact H2.
	Qed.
	
	Print mp.
		mp = fun (P Q: Prop) (H1: P -> Q) (H2: P) => H1 H2:
			 forall P Q: (P -> Q) -> P -> Q

We got **proof term (object)** (following our table from CHC term
constitutes a proof). Let's see another proof for the same prop.

	Theorem mp: forall P Q: Prop, (P -> Q) -> P -> Q.
	Proof.
		intros P Q H1 H2.
		apply H1 in H2.		| H2: Q
		exact H2.
	Qed.

Now the proof term looks a little bit different.

	Print mp.
		mp = fun (P Q: Prop) (H1: P -> Q) (H2: P) => 
			 (fun H3: Q => H3) (H1 H2):
			 forall P Q: (P -> Q) -> P -> Q

Here we have extra inner anonymous function but still it's a proof term.
Let's see another example with **`auto`** now.

	Theorem mp: forall P Q: Prop, (P -> Q) -> P -> Q.
	Proof.
		auto.
	Qed.

	Print mp.
		mp = fun (P Q: Prop) (H: P -> Q) => H:
			 forall P Q: (P -> Q) -> P -> Q

Which non-automatic proof would yield this? Here it is.

	Theorem mp: forall P Q: Prop, (P -> Q) -> P -> Q.
	Proof.
		intros P Q H.
		exact H.
	Qed.

Check what does proof term looks like for a proof containing `destruct`.

## Programming in Coq with inductive types

Instead of famous

> Algorithms + Data Structures = Programs

we will have

> Types + Functions + Theorems = Programs

Actually we can unite Types and Theorems in Dependent Types, but we 
postpone it to the later.

### “Rock / Paper / Scissors” game

Let's try to program the game's logic (see 
[Wikipedia article](http://en.wikipedia.org/wiki/Rock-paper-scissors) 
for dramatical details!) in the following way.

	Inductive weapon: Set = rock | paper | scissors.
	
	Definition next_weapon (w: weapon) : weapon := match w with
		| rock     => paper
		| paper    => scissors
		| scissors => rock
	end.

We want to try this out.

	Eval compute in next_weapon rock.
		paper

	Example ex1: next_weapon rock = paper.
	Proof.
		simpl.		| goal becomes: paper = paper
		reflexivity.
	Qed.
	
We can omit `simple` as `reflexivity` applies this and many other 
tactics (if possible) under the hood.

	Definition wpn_beats (w1 w2: weapon) : Prop := 
		w1 = next_weapon w2
		
Consider another example.

	Example ex2: ~ wpn_beats rock paper.
	Proof.
		intro.
		compute in H.	(* simplification doesn't work here *)
						| H becames: rock = scissors
		discriminate.
	Qed.

This new tactic `discriminate` was developed for exactly such cases:
`smth = smth else`.

#### Rewriting and case analysis for proving theorems

	Theorem wpn_eq_next:
		forall w1, w2: weapon, w1 = w2 -> 
			next_weapon w1 = next_weapon w2.
	Proof.
		intros w1 w2 H.
		rewrite -> H. 	| goal becames: next_weapon w2 = next_weapon w2 
		reflexivity.
	Qed.

You can also use `rewrite` with an arrow reverted to `<-`. Now let's
turn to case analysis.

	Theorem wpn_next:
		forall w: weapon, 
			next_weapon (next_weapon (next_weapon w)) = w.
	Proof.
		intros.
		destruct w; reflexivity.
	Qed.

Tactic `destruct` actually does case analysis. We have three cases
and each could be solved with `reflexivity` so we use `;`.

	Theorem wpn_eq_next_rev:
		forall w1, w2: weapon, 
			next_weapon w1 = next_weapon w2 -> w1 = w2.
	Proof.
		intros w1 w2 H.
		destruct w1; destruct w2; discriminate || reflexivity.
	Qed.

We use `||` to say: try one or other for each subgoal.

	Theorem thm2: forall w1, w2, w3: weapon,
		wpn_beats w1 w2 -> wpn_beats w2 w3 -> wpn_beats w3 w1.
	Proof.
		intros w1, w2, w3.
		destruct w1; destruct w2; destruct w3; 
			discriminate || reflexivity.
	Qed.

	Theorem wpn_decidablity: forall w1, w2: weapon,
		w1 = w2 \/ wpn_beats w1 w2 \/ wpn_beats w2 w1.
	Proof.
		intros w1, w2.
		destruct w1; destruct w2; 
			try (left; reflexivity); right;
			(left; reflexivity) || (right; reflexivity).
	Qed.

		
