# Heterogeneous lists

We continue exploring dependent data structures.

In widely used programming languages with static typing we usually have
just homogeneous lists. E.g. Haskell:

    [Int], [Maybe Double], ...

On the other hand, in dynamically typed languages like Python we are
allowed to build things like:

    [2, true, (1, 0), (false, 1)]

Is it possible to implement such a thing in strongly typed language?
Indeed, it is possible in Coq. But we probably will have to supply
something like `list Type` along with such a heterogeneous list:

    [nat, bool] → [2, true]

See full definition of `hlist` in examples to this lecture and here
we consider a couple examples.

    Definition someTypes : list Set :=
        nat :: bool :: (nat * bool)%type :: nil

It is a list of “types” to be supplied with our heterogeneous list. Here
`%type` is an annotation that allows us to do some type computation
(like computing type product).

    Definition someValues :
        hlist (fun T : S => T) someTypes :=
        HCons 5 (HCons true (HCons (2, false) HNil))

It is a simplest way to map our list of types to
values: just an identity mapping. We can have more complicated mappings.

    Definition somePairs :
        hlist (fun T : Set => T * T)%type
        HCons (1, 2) (HCons (true, false)
            (HCons ((3, true), (1, false)) HNil))

As we learn hot to build heterogeneous lists we want to access them.
We need to build some kind of `cursor`. First we create a membership
function `member` which checks if given type is in the given list of
types. This is usual recursive definition, so we skip it here (you can
look at this in exaples for this lecture).

Next we define the cursor itself.

    Fixpoint hget ls (mls : hlist B ls) :
        member ls -> B elm := match mls with
            | HNil => _ % impossible case, so we wanna return tt
            | HCons _ _ x mls' => _
        end.

Note that we provide `member ls` not as an actual parameter, but as a
part of return type. This is due to our desire to delay this parameter
to make machinery of dependent types work.

We have some problem with returning `tt`: Coq type checker denies our
definition. Recall we always have to convince two parts of Coq that our
definition is OK, namely: type checker and termination checker.

We use some type annotations in such a cases with aid of `in` and
`return`. We use `in` for going inside the type.

## Recursive definition

Recursion and induction conceptually are the same. Sometimes it is
more convenient to define things in terms of `Fixpoint`'s rather then
`Inductive`.

Let's go back to the `ilist` example from previous lecture and redefine
the type using recursion.

    Fixpoint filist (n : nat) : Set := match n with
        | 0     => unit
        | S n'  => A * filist n'
    end.%type

Consider examples of values of this type:

* `tt: filist 0`,
* `(2, tt) : filist 1`,
* `(1, (2, tt)) : filist 2`.

Resulting definition of `fget` for this recursive type is more than
two times smaller then `get` for `ilist`. But there is a gotcha here:
in simple cases recursion is easier than induction, but in hard ones
it is usually not clear how or impossible to use recursion. Coq is more
well-suited for inductive types. The conclusion is: we should know both
tools.

Likewise we can define heterogeneous lists recursively… Consider
`fmember` example.

* `{nat = elm} _ Empty_set : fmember (nat :: nil)

It is a type. The only value of this type is:

    inl er_refl

And it is a cursor for the single element that we build. More
notorious example:

    fmember (bool :: nat :: nil)

We have cursors:

* for the first element: `inl er_refl`,
* for the second element: `inr (inl er_refl)`.

---

We end with unit 2: dependent types. Third unit would be more
practical. The plan is as follows.

1. Proof automation using ltac.
2. Verifiation of cryptographic protocols.
3. Proofs for programming language semantics.
4. Review of **CompCert** — verified C compiler.

## Home work

* Chap. MoreInd (incl. optional tasks).
