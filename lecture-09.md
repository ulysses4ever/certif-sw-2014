> 31.10.2014

# Dependent pattern matching
One of our main instruments was `match smth with ...`. Actually
there are so called _annotations_ which we can add to the match. And
sometimes we have to advice Coq how to interpret the match. We'll
look at different examples of how use annotations wisely.

The full notation looks like:

    match smth as x in (T x1 x2 ...)
        return U with
        | ...
        ...
    end

Here

* `smth` — _discriminee_.
* `x` - _alias_. It's often usefull if `x` is an expression.
* `T` is a type of the discriminee
* `x1`, `x2`, …  are some  bindings
* `U` — type. Return type of this match. It can depend on alias,
    bindings, ant type `T`.

Coq somethings can infer `as`, `in` and `return` sections, but
sometimes it's imporsible. The problem of type inference with
dependent type is **undecidable**, it's prooved. Coq, in fact, uses
different kinds of heuristics.

Let us consider an example: `length_indexedlists`. The type is going
to have two arguments now:

    ilist nat n

where `n: Set`, `nat: Type`. Often we need this kind of lists.

The inductive type `Inductive ilist: nat -> Set` is _type family_.
The `ilist` becomes a type if we provide the necessary arguments.
E. g. `ilist nat 5` is a particular type. The `x1`, `x2` bindings
are the arguments, for example the lists's length `n`.

One of the simplest functions we can write about `ilist` is

    Fixpoint app n`(ls1: ilist n1) n2 (ls2: ilist n2): ilist (n1 + n2)

The `n1 + n2` in the definition is of interest here. Type checking
takes place in the time of compilation. But in this time we don't
know the lists length. This check is called _breaking face
distinction_. Here in the present of dependent types there is no
such strictly separated compile and runtime time. The check takes
place during runtime.

In the `app` example in Coq version 8.3 would not inferer types. But in 8.4
version it's already OK. So Coq is rapidly develop, in particular,
new heuristics are added.

Let's `Print app` to see all the annotations…

* `{struct ls1}` annotation means we are doing recursion on the first argument `ls1`.

Why there is no `n1` in `in` section? We can use the old `n1` here,
but it's not a good idea. `n1` is changing all the time because of
the recursion, but `n2` is fixed. `n` is equal to `n1` but they are
not the same. This is the reason.

Let's define function of injecting and unjecting regular list
to/from a lengthed list.

    Fixpoint inject (ls: list A): ilist (length ls)

Once again, dependent types allow us not to define a lot of
theorems, as all the facts would be built in the type definition.
For example the fact that "injected" list equals to the origin one.

    Fixpoint unject n (ls: ilist n): list A

Here `n` would be an implicit argument.

    Theorem iject_inverse: forall ls, unject (inject ls) = ls.
    Proof.
        inductin ls; try (simpl; rewrite IHls); reflexivity.
    Qed.

But sometimes we get a lot of troubles. Let's proove the inverse
theorem.

    Theorem uject_inverse: forall n (ls: ilist n), ls = inject (unject ls).

We'll get the error of defining the theorem. It's not clear for Coq
that `length (unject ls)` is equal to `n` as in definition of `ilist`.
We should prove it to Coq.

    Lemma unject_length: forall n (ls: ilist n), length(unject ls) = n.

Still the same error. The Coq can't get the fact from the Lemma.
To state the theorem we need to include the proof in the definition of the theorem.

    Theorem unnject_inverse: forall n (ls: ilist n) (pf: length(unject ls) = n),
        ls = match pf in (_ = n) return ilist n with
          eq_refl => inject (unject ls)
        end.
    Proof.
        induction ls.
        simpl. (* it's hard to prove without a special knowledge *).
        rewrite (UIP_refl _ _ _).
        (* Goal: Nil = Nil *)

The equality `(_ = n)` is just a some inductive type (as all in Coq)
in some special notation. Equality is an inductive type with two
arguments: left and right.

And the Coq is convinced, the theorem is stated. We can consider
this now as just a trick.

The **UIP** stands for _uniquness of identity proofs_. This usually
means that if we have something of a form `A = A` then there is
unique proof of it.

We should assume `A = A` as an axiom. This comes from Aristotle
In our case `UIP_refl` is applied for the axiom `0 = 0`. And it seems to be the only possible way.

    _(long Proof)_

## Conclusions

The main working tool here was rewriting with `UIP_refl`.

### Ideas

1. stating theorem
    - match on proof of equality
2. `UIP_refl`
    - (A = A)
3. `rewrite (...) at 1` to rewrite only particular occurrences.
4. `generalize (some_expr)`
    - `forall n: nat, n = n` is a generalization of `2 = 2`
    - in the proof we've generalized goal
5. `repeat` for repeating tactics

Our next task is to implement function `hd` which takes the first
element of a list. And we are going to make it safe: for example,
make it impossible to apply `hd` to `ilist 0` (there are other ways
to do it "safety").

    Definition hd1 n (ls: ilist (S n)): A :=
      match ls with
        | Cons _ h _ => h
      end.

Let's `Print hd`. We've got `Id` in the impossible case.

Let's write it manually.

    Definition hd2 n (ls: ilist (S n)): A :=
      match ls in (ilist n')
        return (match n' with O => unit | S _ => A end) with
      | Nil => tt
      | Cons _ h _ => h
      end.

Let's look again at the automaticly generated `hd1`. Look at the return section in the match.
It is called _convoy pattern_. It looks like:

    v | (func x => v) x

In theory it's called `\eta-equivalence`. We have to use convoy pattern when there is not enough information about type.

See manual definition of convoy pattern in supplied examples.

## Getting elements

Let's us define the “index” type.

Why doesn't the second from the end example work, but the next do
work? Why? In the former there were no connection specified between
`idx'` and `ls'`. In the next one we relate them by

    n': idx in fin n'

and

    ilist (pred n')

We'll skip the last version because the previous one is actually works.

Conwoy pattern is a tool that allows to provide more relations
between dependent types.

The result is that it's impossible to invoke the `get` function with
incorrect arguments.

## Map function

    Fixpoint imap ...

We'll prove an interesting theorem.

    Theorem get_imap: forall n (idx: fin n) (ls: ilist A n),
        get (imap ls) idx = f (get ls idx).

Computationally the right part is better. So we want to prove a
theorem on the correctness of this optimization.

> ... I've got a new version of Ubuntu this weak. New version -- new problems.

**Proof.** `destruct` on the match discriminee doesn't work because
of the inductive types. There is another tactic for it:
`dependent destruction`.

## Home task
1. Two chapters: Rel and Proof Objects. Remember, you should solve it with optional tasks (there are only such tasks there).
