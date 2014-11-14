# Unit 3 (more practical one)

## Proof search automation

We consider two approaches for automation:

* more clever using of `auto`,
* other automation tactics (like Chlipala's `crush`).

Taking first one we'll try to understand how `auto` works. In fact
this is not just searching through database. Instead it is a kind of
**logic programming** (in Prolog sense). We'll try to omit details
directly connected with this LP.

### Unification for relational definitions

Consider simplest example of binary operation on naturals: `plus`.
We can give _computational_ definition for it: `m + n` means adding 1
to `n` for `m` times. We can give another, **relational** definition:

* (m, n, p) ∊ R  iff  m + n=p

This definition is quite formal. We can give, say, more “accessible”
one introducing two clauses:

1. (0, m, m) ∊ R for all m.
2. if (m, n, p) ∊ R then (S m, n, S p) ∊ R.

Trying to prove something easy we get:

* (3, 1, 4) ∊ R ← (2, 1, 3) ∊ R ← (1, 1, 2) ∊ R ← (0, 1, 1) ∊ R

We do not use any computation here. Just a constructor `S` from
definition of naturals.

We try to prove that this relational definition of plus, call it `plusR`,
coincide with built-in `+`. Cf. `Theorem plus_plusR` and
 `Theorem plusR_plus` in examples for this lecture.

Proving things like `plusR 3 4 7` involves repetitive tries of using of
the constructors: `PlusO` or `PlusS`. In fact this is the thing which
is done by `auto`. We can convince ourselves using special tactic:
**`info_auto`** which prints the steps performed by `auto` on its way to
a goal.

It is a general approach:

> while goal not proved {apply all constructors until one of them succeeds}

This procedure traverses implicit **proof tree**. The number of possible
paths from root to a leaf is _n_<sup>_m_</sup>, where _m_ is number of
constructors and _m_ is a maximum depth for us to try. Our `auto`
tactic has _m_ equal to 5.

Let's inspect the ways to prove more complicated things like subtraction:

    exist x, PlusR x 3 7

To eliminate `exist` we can use `eexist`: recall this `e`-prefixed
tactics introduce new variables. Now we have something like:

    PlusR ?105 3 7

Now we can fall back to our basic tactic: just trying to apply some
constructor. We have to apply `PlusS` five times and `PlusO` once. It is
more than `auto` limit (which is 5) but we can suggest `auto` how many
times to try.

We end up in this subtraction example with the oneliner:

    eauto 6.

### Unification for functional definitions

Our next goal is to learn how to use such relational style proofs
which are called **unification** in logic programming to functional
definitions.

We prove functional analogues of our relational definition for `PlusR`
for `+`. It allows for translate our proofs from previous subsection
to the `+`.

### Case study: Linear expressions

Consider a class of expressions built with one operation: `+` and one
variable (say, `x`). We want to prove that any expression of this type
could be written in such a form: _k_*_x_ + _n_.

First we go the whole way with proof using as much inline automation
as we can. Second,
we take another approach: we define function crush which is essentially
an `auto` on steroids. It alone will solve most of auxiliary and the main fact of this theory of linear expression.

See the whole listing in examples to this lecture.

## Mutually inductive types

We're going to define two interconnected types:

* `even_list`,
* `odd_list`.

A value of one type is obtained through appending an element to the other. We try to define all the basic function on lists.

We'll have a number of problems with this types. First, the induction
principle generated automatically is too weak. We have to advice Coq on
how to do mutual recursion on mutually inductive types.

## Home task

* To `crush` chap. More Coq of SF
