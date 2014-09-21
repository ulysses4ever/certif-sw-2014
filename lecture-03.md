## More inductive types

Types we defined so far was not _that_ inductive. In fact they are so
called _enumerates_. E.g.

	Inductive bool: Set := true | false.
	
Now we define “real” inductive type, one of the most import one is the
following.

	Inductive nat: Set :=
		| O: nat 		   (* we use capital letter O, not zero char. *)
		| S: nat -> nat.

Here we have some differences with previous definition:

*	leading `|` is just a matter of a beauty;

*	we explicitly name type of **constructors** (`O` and `S`) we listed
	(`nat` and `nat -> nat` correspondingly).

This is quite old idea for definition of `nat`'s: it dates back to approx.
beginning of XXth century and is called _unary representation_.

Let's start to define functions on our `nat`'s.

	Definition pred(n: nat): nat := match n with
		| O 	=> O
		| S n' 	=> n'
	end.

We use `Eval` to test it as usual.

	Eval simpl in (pred (S(S(SO)))).
		> S(SO)
		
We use `Eval simpl` instead of `Eval compute` for simple substitutions 
like the one coined in this example.

We have important properties of inductive types:

*	if two values built by different constructors, then they are not
	equal;
	
*	constructors are injective.

Let's proove second one in case of `nat`'s.

	Theorem S_inj: forall n, m: nat, S n = S m -> n = m
	Proof.
		injectivity 1. 	(* one for one premise: S n = S m   *)
						(* the goal becomes: n = m -> n = m *)
		trivial.
		
		Restart.		(* let's try different way for a proof *)
		congruence.		(* see below *)
		
		Restart.		(* one more way *)
		intros n m H.
		assert (H1: forall n: nat, n = pred (S n)).	(* see below *)
			reflexivity.
			
		rewrite -> H1 with (n).
		rewrite -> H1 with (m).
		rewrite -> H.
		reflexivity.
	Qed.

Tactic `congruence` is a complete decision procedure for the theory of
equality, uninterpreted functions and inductive types.

Tactic `assert` means: I wanna use such a hypothesis and I will prove it
first, no matter what a current goal and hypothesis are.

Let's turn back to the theorem from the last lecture. We start with one
auxillary function.

	Definition toProp (w: weapon): Prop := 
		| rock 	=> True
		| _		=> False
	end.

	Theorem rock_n_paper: rock <> paper.
	Proof.
		intro. 					(* H: rock = paper // False *)
		change (toProp paper).	(* H: rock = paper // toProp paper *)
		rewrite <- H.			(* // True *)
		apply I.				(* surprise! *)
	Qed.

Let's turn to defining more functions for our `nat`'s. Now we want an 
addition.

	Fixpoint plus(n m: nat): nat := match n with
		| O 	=> m
		| S n' 	=> S plus (n' m)
	end.

We use recursion here and we need to use keyword `Fixpoint` to indicate
this.

Coq's functions should follow important rule:

>	Every Coq function should **terminate**.

This implies that _Coq is not Turing complete_. Anyway let's continue
with proving some properties of an addition.

	Theorem O_plus_n: forall n: nat, plus O n = n.
	Proof.
		intro.
		(* simpl. *)
		reflexivity.
	Qed.

	Theorem n_plus_O: forall n: nat, plus n O = n.
	Proof.
		intro.
		destruct n.
		reflexivity. 	(* n: nat // plus (S n) O = S n *)
		simpl. 			(* n: nat // S (plus n O) = S n *)
						(* this is a dead end *)
		
		Restart.
		intros.
		induction n.
		reflexivity.	(* solves goal for base of induction: plus O O = O *)
						(* now we have to prove induction: 
							IHn: plus n O = n // plus (S n) O = S n *)
		simpl.			(* goal: S (plus n O) = S n*)
		rewrite -> IHn.	(* S n = S n *)
		reflexivity.
	Qed.

In fact we have so called **induction principle** for each inductive type.
It is defined for us by Coq and looks like the following.

	nat_ind: forall P: nat -> Prop, P O 
		-> (forall n: nat, P n -> P (S n)) -> forall n: nat, P n

We leave proofs for other well-known functions and their properties as
an exercise.

## Data Structures

### Pairs

	Inductive nat_pair: Set :=
		| pair: nat -> nat -> nat_pair.
	
	Check (pair O (S(SO)))
	
### Lists

	Inductive nat_list: Set :=
		| NNil: nat_list
		| NCons: nat -> nat_list -> nat_list.
	
	Check NNil.
		> nat_list
	Check NCons (S O) NNil.
	
	forall P: nat_list -> Prop: P NNil 
		-> (forall (n: nat) (lst: nat_list), 
			P lst -> P (NCons n lst)
		->	forall lst: nat_list, P lst.

Let's define length of a list.

	Fixpoint nlength (l: nat_list): nat := l match with
		| NNil 			=> O
		| NCons _ l'	=> S (nlength l')
	end.
	
Now: concatenation of list.

	Fixpoint napp (l1 l2: nat_list): nat_list := l1 match with
		| NNil 			=> l2
		| NCons n l1' 	=> NCons n (napp l1' l2)

Let's prove a theorem connecting `nlength` and `napp`.

	Theorem nlength_napp: forall l1 l2: nat_list,
		nlength (napp l1 l2) = plus (nlength l1) (nlength l2)
	Proof.
		induction l1.
		reflexivity.
		(* 	IHl1: nlength (napp l1 l2) = plus (nlength l1) (nlength l2)
			// nlength (napp (NCons n l1) l2) = plus ...*)
		rewrite IHl1.
		reflexivity.
	Qed.

### Home reading

* Software Foundations, chap. on Lists
