## Propositional Logic As a Part of Type System

Propositional logic is nothing special in Coq: it's just a part of
inductive type system. Recall that `True` is an inductive type with
only one value `I` and `False` is an empty inductive type. At the same
time `not A` is a function which takes `A: Prop` and returns `False`.
Interestingly conjunction and disjunction are parametrized 
inductive types, not functions.

	Inductive and(A, B: Prop): Prop :=
		conj: A -> B -> A /\ B

	Inductive or(A, B: Prop): Prop :=
		| or_left:  A -> A \/ B
		| or_right: B -> A \/ B

Why do we need propositional logic in our system for construct correct
software? It turns out that every program could be (more or less) split
into two parts: logical one and programming one. Second one usually
concerned with program **domain**.

	forall ls1 ls2: list nat,
		length ls1 = length ls2 \/  length ls1 + length ls1 = 6 (*premise*)
			-> length (ls1 + ls2) \/ length ls1 = length ls2    (*conclusion*)
			
This proposition is shaped like: `A \/ B -> C \/ A`. How would we prove
this? We have to consider two cases, first one:
`if A holds then C \/ A holds` which is logically true. We can factor out
this case automatically using `intuition`. And second one:
`if B holds then C \/ A holds` which couldn't by proved by means of
pure logic exclusively. Instead we have to apply some facts about 
(definition of) lists. We can search on facts about `length` with:
`SearchAbout length`. We see that `app_length` can help us and we use
`rewrite app_length`. Then we have only one simple propositional fact
which we can prove with `tauto` which is _complete decision procedure_
for propositional logic.

We have some more automation tactics, following this distinction between 
logics and domain:

* logics: `intuition`, `tauto`, `firstorder`;
* domain: `SearchAbout`, `SearchPattern`.

We also have one great tactic called `omega` to prove things about 
naturals.

## Inductive predicates

We continue with exploring automation. One more popular automation
tactics is `auto` which just tries all known tactics from its database
(so it's quite “dumb” tactic).

Another tactic which looks similar to destruct is `inversion`.

	Inductive isZero : nat -> Prop :=
		IsZero : isZero 0.

	Theorem t: isZero 1 -> False.
	Proof.
		inversion 1. (* no more subgoals *)
	Qed.

More complicated inductive predicate is `even`.

	Inductive even : nat -> Prop :=
		| EvenO : even O
		| EvenSS : forall n, even n -> even (S (S n)).

We can prove facts about `even` merely using `constructor` tactics.

	Theorem even_0 : even 0.
		constructor.
	Qed.

	Theorem even_4 : even 4.
		constructor; constructor; constructor.
	Qed.

Clearly we want some automation here.

	Hint Constructors even.

	Theorem even_4' : even 4.
	  auto.
	Qed.

Let's see how we can apply above mentioned `inversion` here.

	Theorem even_1_contra : even 1 -> False.
	  inversion 1.
	Qed.

### Case Study: Insertion Sort

We want to have certified version of insertion sort algorithm 
implementation. Of course we will use Coq to implement this.

First, we should define the property of a list to be sorted.

	sorted: 
		nil
		[x]
		x, (y :: l) is sorted, x ≤ y => x :: y :: l is sorted
		
It turns out that we should have a notion to state that input list and 
resulting sorted list are equal.

	l ~ l' iff
		they have the same elements (equal number of every elements)
		
The basic property that lies in heart of insertion sort (and we will
have to prove it):

	x :: l ~ ins x l

where `ins` is a function for ordered insertion in a list.

See full proof in `insertSort.v`.

## Home Assignment

* Software Foundations, chap. 5: More Coq
