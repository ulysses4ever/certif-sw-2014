## Inductive types (continued)

We define binary tree inductive type as following.

    Inductive nat_btree: Type :=
        | NLeaf : nat_btree
        | NNode : nat_btree -> nat -> nat_btree -> nat_btree
        
Note that we have empty leaf here. 

Our problem with such a kind of
definitions is that we do not have enough polymorphism. In this
particular case we can't have _n-ary trees_ or trees of `Bool` etc.

## Parametrized Types

    Inductive prod (X Y: Type) := pair : X -> Y -> prod X Y

Here `prod` is a function with two `Type`-arguments.

    Check pair.
        : forall X Y: Type, X -> Y -> prod X Y
    
    Check pair nat nat (S O) (S (S (S O))).
        : prod nat nat

We really want add **type inference** to this parametrized types in
order not to, say, repeat ourselves.

    Arguments pair {X} {Y} _ _.
    
    Check pair (S O) (S O).
        : prod nat nat

We have more advanced way to use `Arguments` and defining parametrized 
types.

    Set Implicit Arguments.
    
    Section list.
        Variable T: Type.  (* now T becomes implicit parameter
                              for all of the following *)
        Inductive list := 
            | Nil:  list
            | Cons: T -> list -> list.
        
        Fixpoint length(l: list): nat := match l with
            | Nil       => O
            | Cons _ l' => S (length l')
        end.
    End list.
    
    Check list.
        : forall T: Type, list T
    
    Check length.
        : forall T: Type, list T -> nat.
    
    Arguments Nil [T]. (* helps Coq infer type for Nil below *)

    Check length (Cons O Nil)
        : nat
        
Imagine, that we did not add two clauses containing `Arguments` above.
Then the right way to use `length` is the following.

    Check length nat (Cons nat O (Nil nat)).
        : nat.

## Induction principle (again)

A little bit of theory.

    Check nat_ind.
        forall P: nat -> Prop,
            P O ->
            (forall n: nat, P n -> P (S n)) ->
            forall n: nat, P n
    
    Print nat_ind.
        fun P: nat -> Prop => nat_rect P
        
Here `_rect` means _recursion on types_.

    Check nat_rect.
        forall P: nat -> Type,
            P O ->
            (forall n: nat, P n -> P (S n)) ->
            forall n: nat, P n

Recall we have three _universes_: `Type`, `Set`, `Prop`. But thing are a 
little more involved: `Set`, `Prop` ∊ `Type`. So `Type` includes `Set` and 
`Prop`. And `nat_ind` is a part of a universe of propositions, `nat_rect` — of 
types. We should have some analogy of this in the universe of sets. See below.

    Print nat_rec
        fun (P: nat -> Set)(f: P O)(f0: forall n, Pn -> P (S n)) => 
        fix F (n: nat): P n := match n as n0 return (P n0) with
            | O     => f
            | S n0  => f0 n0 (F n0)
        end

This `nat_rec` is anonymous function (`fun args => body`) has three arguments: 
predicate, recursion base, recursion step. Then the body is defined via
_recursive_ anonymous function (which is reflected by `fix`). This `fix` has
following structure: `fix name (args): type := body` and `body` uses `name`.
Let's skip the type of function inside `fix` and `return`-line. Interestingly,
result of the body depends on the argument: it is wither `P O` or `P (S n)` 
(and `n` is parameter here, so we have countably infinite number of return types).
This fact: _return **type** depends on arguments_ is reflected by `return` clause.

We'd' probably prefer simpler definition of induction and we actually can define
it ourself simpler. Let's see this.

    Section nat_ind'.
        Variable P: nat -> Prop.
        Hypothesis O_Case -> P O.
        Hypotheses S_Case -> forall n, Pn -> P (S n).
        Fixpoint nat_ind' (n: nat): P n := match n with 
            | O => O_Case
            | S n => S_Case (nat_ind' n') (* using Set Implicit Args? *)
        End nat_ind'.

We remind that every time we define inductive type `T` we get all three:
`T_ind`, `T_rec`, `T_rect`. There are cases though when these automatically
generated objects are too weak to prove what we want. In such cases we have to
define similar but more powerful objects by ourselves.

Let's see what these generated object are good for. Recall usual definition of 
`plus` for `nat`'s.

    Fixpoint (n: nat): nat -> nat := match n with
        | O     => fun m => m
        | S n'  => S (plus n' m)
    end

Now we give definition for `plus` _without explicit recursion_.

    Definition plus' 

### Home reading

* Software Foundations, chap. Poly
