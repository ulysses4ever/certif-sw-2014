# Unit 2. Programming with Dependent Types

## Case Study: `pred` function

This time we we'll try our best to define predecessor function. Recall 
our first definition.

	Definition pred (n: nat): nat := match m with
		| O 	=> O
		| S n' 	=> n'
	end.
	
	Check pred.
		nat -> nat

Following Curry-Howard correspondence we can supply proof instead of 
function body.

	Definition pred' (n: nat): nat.
		destruct n as [|n'].
		exact O.
		exact n'.
	Defined.
	
	Check pred'.
		nat -> nat	

If we use `Print pred'` we'll get the same body as in first example with 
`pred`. Here are some other versions.

	
	Definition pred'': forall n: nat, nat.
		intro n.
		(* the same as in pred *)
		destruct n as [ |n'].
		exact O.
		exact n'.
	Defined.
	
	Definition pred''': nat -> nat.
		destruct 1  as [ |n'].
		(* the same as in pred *)
		exact O.
		exact n'.
	Defined.
	
	Definition pred'''': nat -> nat.
		exact (fun n => match n with
			| O 	=> O
			| S n' 	=> n'
			end).
	Defined.

	Definition pred'''': nat -> nat.
		refine (fun n => match n with
			| O 	=> _
			| S n' 	=> _
			end).
		exact O.
		exact n'.
	Defined.

We have two problems here. The first one is that 
in this kind of definitions the type of term being 
defined is too vague. This is not how we construct certified SW.
The second one is `pred 0 = 0` — this actually a hack, we don't have such
a thing as predecessor of zero. For this problem we have two solutions:

1. 	Define `pred` only for positive numbers. Here we have to supply
	a proof of positiveness for each number we use as an argument to 
	`pred`.

2. 	Inform programmer on the problem in run-time.

Our future plans are as follows

1. Address problem #2 with solution #1.

2. Address problem #1.

3. Address problem #2 with solution #2.


### Predecessors only for positives

Let's start with auxiliary lemma.

	Lemma zgtz: 0 > 0 -> False. (* zero greater than zero *)
		inversion 1.
	Qed.

Next we inspect a Coq feature which is called **subset type**.

	Print sig. 
	(* 
		Indictive siq (A: Type)(P: A -> Prop): Type := 
			exist : forall x: A, P x -> {x | P x}
	*)

Now we're ready to define our first _strong_ `pred` function.

	Definition pred_strong1 (s: {n: nat | n > 0}): nat := match s with
		| exist O pf (* it's a proof that 0 > 0 *) =>
			match zgtz pf (* here we have False and nothing to prove any more *)
			end 
		| exist (S n') _ => n'
	end.

In Coq we can't call this function with zero, but if we exctract it to 
some other language, there programmer can do this. Then he will have 
failed assertion at run-time.

Let's try to use above defined strong `pred` function.

	Eval compute in (pred_strong1 (exist 2 (Gt.gt_Sn_0 1))).

Here we found `Gt.gt_Sn_0` fact while `SearchPattern (_ > _)`, it tells
us that `forall n: nat, S n > 0`.

A kind of weird thing here is that for computing 1 we had to use 1 (as
an argument to `Gt.gt_Sn_0`. In real application we usually have such a
proof on hand and do not use `Gt.gt_Sn_0`.

### More specific type for `pred`

Let's turn to Problem #1 with too vague type of `pred`. Our desired type
instead of `nat -> nat` would be:

	forall n: nat, n > 0 -> {m: nat | S m = n}

Let's define `strong_pred2`.

	Definition strong_pred2: forall n: nat, n > 0 -> {m: nat | S m = n}.
		intros.
		destruct as [ | n0].
		elimtype False. (* exchange goal for a False *)
		inversion H. (* H: 0 > 0 *)
		
		exists n0.
	Defined.

The return type of the function is quite tricky to use:

	Eval compute in (pred_strong2 (exist 2 (Gt.gt_Sn_0 1))).
		= exist (fun m: nat => 2 = S m) 1 eq_refl : {m: nat | 2 = S m}

We don't like to look at this so we introduce special `Notation`.

	Notation "[ e ]" := (exist _ e _).

Now the above mentioned `Eval` gives:

	[ 1 ] : {m: nat | 2 = S m}

Previous definition of `strong_pred2` doesn't show up nice structure.
We try to improve it.

	Definition strong_pred2': forall n: nat, n > 0 -> {m: nat | S m = n}.
		refine (fun n: nat => match n with
			| O 	=> fun pf => False_rec _ _
			| S n' 	=> fun _  => [ n' ]
		end).
		inversion pf (* pf: 0 > 0 *).
		reflexivity.
	Defined.

### Error detection

Let's address second problem with `pred 0` again. We'll use special
sum type.

	Print sumor.
		= Inductive sumor (A: Type)(B: Prop): Type :=
		| inleft: A -> A + {B}
		| inright: A -> A + {B}.

	Definition pred_strong3: forall n: nat,
			{m: nat | S m = n} + {n = 0}.
		refine (fun n: nat => match n with
			| O 	=> inright _ _ 
				(* A: prop would be inferred so no need for _ for it *)
				
			| S n' 	=> inleft _ [ n' ]
		end); reflexivity.
	Defined.
	
	Eval compute in pred_strong3 10.
		= inleft [9]: {…} + {…}
	
	Eval compute in pred_strong3 0.
		= inright eq_refl: {…} + {…}

## Decidable Proposition Types

	Print sumbool.
	(*
		Inductive sumbool (A B: Prop): Type :=
			| left:  A -> {A} + {B}
			| right: B -> {A} + {B}
	*)

	Definition eq_nat_dec: forall n m: nat,
			{n = m} + {n <> m}.
		refine (fix f (n m: nat): {n = m} + {n <> m} := match n, m with
			| O, O 			=> left _ _
			} S n', S m' 	=> if f n' m' then (left _ _) else (right _ _)
			| _, _ 			=> right _ _
		end); congruence.
